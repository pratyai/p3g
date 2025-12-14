import dace
from dace import SDFG, Memlet, subsets
from dace.sdfg import nodes, state as states
from dace.sdfg import utils as sdfg_utils
import networkx as nx


def expand_scalars(sdfg: SDFG):
    """
    Expands transient scalars in LoopRegions to arrays indexed by the loop variable,
    effectively privatizing them to break loop-carried dependencies.
    """
    # Iterate over all nodes to find LoopRegions.
    # Process top-down to handle outer loops first.
    for node, parent in sdfg.all_nodes_recursive():
        if isinstance(node, states.LoopRegion):
            _expand_scalars_in_loop(node, node.sdfg)


def _expand_scalars_in_loop(loop: states.LoopRegion, sdfg: SDFG):
    # 1. Identify candidates
    # Candidates are transients defined in the SDFG (or parent SDFG) that are used inside this loop
    # and are "dominated by write" inside the loop body.

    candidates = set()

    # Find all data used in the loop
    read_set = set()
    write_set = set()

    # Build CFG of the loop body.
    if not loop.nodes():
        return

    cfg = nx.DiGraph()
    for n in loop.nodes():
        cfg.add_node(n)
    for e in loop.edges():
        cfg.add_edge(e.src, e.dst)

    start_node = loop.start_block

    # Analyze usage per node
    node_writes = {}  # node -> set of data written (fully)
    node_reads = {}  # node -> set of data read (or partially written)

    # Helper to check if a memlet covers the whole scalar
    def is_full_scalar_write(memlet, data_name):
        if memlet.data != data_name:
            return False
        # Assuming scalar, subset should be "0" or empty or full range
        return True

    def get_accesses(graph_node):
        r = set()
        w = set()
        full_w = set()

        if isinstance(graph_node, states.SDFGState):
            for dnode in graph_node.data_nodes():
                desc = sdfg.arrays[dnode.data]
                if not desc.transient:
                    continue
                if desc.shape != (1,) and desc.shape != ():
                    continue  # Only scalars for now

                # Check edges
                in_edges = graph_node.in_edges(dnode)
                out_edges = graph_node.out_edges(dnode)

                if out_edges:
                    r.add(dnode.data)

                if in_edges:
                    w.add(dnode.data)
                    # Check if it's a full write (not WCR)
                    is_wcr = any(e.data.wcr is not None for e in in_edges)
                    if not is_wcr:
                        full_w.add(dnode.data)

        elif isinstance(graph_node, states.LoopRegion):
            for sub_node in graph_node.nodes():
                sr, sw, sfw = get_accesses(sub_node)
                r.update(sr)
                w.update(sw)
                # Conservatively, we don't propagate full writes from nested loops
                # as we don't know if the loop executes > 0 times.

        elif isinstance(graph_node, states.ConditionalBlock):
            for _, branch_body in graph_node.branches:
                # branch_body is a ControlFlowRegion (Graph)
                for sub_node in branch_body.nodes():
                    sr, sw, sfw = get_accesses(sub_node)
                    r.update(sr)
                    w.update(sw)
            # Conservatively no full writes from conditional

        return r, w, full_w

    # Collect accesses
    all_transients = set()
    for n in loop.nodes():
        r, w, fw = get_accesses(n)
        node_reads[n] = r
        node_writes[n] = fw  # Track full writes for dominance
        all_transients.update(r)
        all_transients.update(w)

    # Check dominance for each transient
    for data in all_transients:
        # Check if defined (full write) dominates all reads.
        # A read at node N is valid for privatization IF every path from start_node to N
        # goes through a node M where data is in node_writes[M] (and M can be N).

        can_privatize = True

        # Find all reading nodes
        reading_nodes = [n for n in loop.nodes() if data in node_reads[n]]
        if not reading_nodes:
            continue

        # Check reachability on the subgraph WITHOUT write nodes.
        # If we can reach a read node without hitting a write node, then it's NOT privatizable.
        # Treat a node that Reads AND Writes as "Read occurs before Write" for safety.

        # Graph of nodes that do NOT fully write 'data'
        non_writing_nodes = [
            n for n in loop.nodes() if data not in node_writes.get(n, set())
        ]
        subgraph = cfg.subgraph(non_writing_nodes)

        if start_node not in non_writing_nodes:
            # Start node writes it.
            if data in node_reads.get(start_node, set()):
                # Read at start, implies loop carried or uninitialized read
                can_privatize = False
            else:
                # Start node writes it, and doesn't read it. So it dominates.
                can_privatize = True
        else:
            # Start node does NOT write it.
            # Check reachability of any node in `reading_nodes` from `start_node`
            # passing only through `non_writing_nodes`.

            # If start_node is in non_writing, we start search.
            reachable = set()
            if start_node in non_writing_nodes:
                # Simple BFS
                q = [start_node]
                seen = {start_node}
                while q:
                    curr = q.pop(0)
                    reachable.add(curr)
                    for succ in subgraph.successors(curr):
                        if succ not in seen:
                            seen.add(succ)
                            q.append(succ)

            # If any reading node is in reachable, we have a problem
            if any(rn in reachable for rn in reading_nodes):
                can_privatize = False

        if can_privatize:
            candidates.add(data)

    # 2. Apply Expansion
    # For each candidate:
    # - Change Array descriptor shape: [1] -> [Range]
    # - In this loop, replace access `data[0]` with `data[loop_var]`

    if not candidates:
        return

    print(f"Expanding scalars in loop {loop.label}: {candidates}")

    # Get Loop range
    loop_var = loop.loop_variable

    # We attempt to extract the loop upper bound from the condition string.
    import ast

    loop_limit = None
    # Naive parsing: assume "var < Limit"
    cond = loop.loop_condition.as_string
    parts = cond.split("<")
    if len(parts) == 2:
        limit_str = parts[1].strip().rstrip(")")
        # Try to resolve symbol
        loop_limit = limit_str

    if not loop_limit:
        raise ValueError(
            f"Could not determine loop bound for expansion in {loop.label} from condition: {loop.loop_condition.as_string}"
        )

    for data in candidates:
        desc = sdfg.arrays[data]

        # 1. Update Descriptor
        # Add dimension: Change scalar shape [1] or () to [loop_limit]
        sym_limit = dace.symbolic.pystr_to_symbolic(loop_limit)

        new_shape = (sym_limit,) + desc.shape if desc.shape == () else (sym_limit,)

        # Replace Scalar with Array
        if isinstance(desc, dace.data.Scalar):
            new_desc = dace.data.Array(
                dtype=desc.dtype,
                shape=new_shape,
                transient=desc.transient,
                storage=desc.storage,
                location=desc.location,
                allow_conflicts=desc.allow_conflicts,
                lifetime=desc.lifetime,
                alignment=desc.alignment,
                debuginfo=desc.debuginfo,
                offset=desc.offset,
                may_alias=desc.may_alias,
            )
            sdfg.arrays[data] = new_desc
        else:
            # Already an array, just update shape
            desc.shape = new_shape
            desc.strides = desc.compute_strides(desc.shape)
            desc.total_size = desc.compute_total_size(desc.shape)

        # 2. Update Memlets in the loop
        # Prepend `loop_var` to the access indices.

        for node in loop.nodes():
            if isinstance(node, states.SDFGState):
                for edge in node.edges():
                    memlet = edge.data
                    if memlet.data == data:
                        # Create new subset: [loop_var]
                        new_subset = dace.subsets.Range(
                            [
                                (
                                    dace.symbolic.pystr_to_symbolic(loop_var),
                                    dace.symbolic.pystr_to_symbolic(loop_var),
                                    1,
                                )
                            ]
                        )
                        memlet.subset = new_subset
            elif isinstance(node, states.LoopRegion):
                # Recursively update memlets in nested regions
                _update_memlets_recursive(node, data, loop_var)


def _update_memlets_recursive(region, data_name, index_str):
    if isinstance(region, states.SDFGState):
        for edge in region.edges():
            memlet = edge.data
            if memlet.data == data_name:
                new_subset = dace.subsets.Range(
                    [
                        (
                            dace.symbolic.pystr_to_symbolic(index_str),
                            dace.symbolic.pystr_to_symbolic(index_str),
                            1,
                        )
                    ]
                )
                memlet.subset = new_subset
    elif isinstance(
        region, (states.LoopRegion, states.ConditionalBlock)
    ):  # ConditionalBlock needs handling
        nodes_to_process = (
            region.nodes() if isinstance(region, states.LoopRegion) else []
        )
        if isinstance(region, states.ConditionalBlock):
            for _, branch in region.branches:
                nodes_to_process.append(branch)

        for node in nodes_to_process:
            # If node is a state or region
            if isinstance(
                node,
                (
                    states.SDFGState,
                    states.LoopRegion,
                    states.ConditionalBlock,
                    dace.sdfg.state.ControlFlowRegion,
                ),
            ):
                _update_memlets_recursive(node, data_name, index_str)
