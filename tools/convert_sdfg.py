"""
This file converts a DaCe SDFG into a P3G Graph representation.

Some notes:
- We likely need a preprocessing pass
- What if nested SDFGs have symbols that shadow parent SDFG symbols (and array names)?
- What about symbol updates on interstate edges? (and array )
- What about array access in condition expressions or loop bounds?

"""

import dace
import sys
import os
from dace.sdfg import SDFG
from dace.sdfg.utils import dfs_topological_sort
from dace.transformation.passes.analysis.loop_analysis import (
    get_loop_end,
    get_init_assignment,
    get_loop_stride,
)
from dace.sdfg.nodes import AccessNode, Tasklet, MapEntry, MapExit, NestedSDFG
from dace.sdfg.state import LoopRegion, SDFGState, ConditionalBlock

from pysmt.shortcuts import Symbol, INT, TRUE, And, GE, LE, Plus, Int, simplify

# Allow imports from parent directory
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from p3g.p3g import GraphBuilder, Graph, PysmtCoordSet
from tests.utils import print_p3g_structure


@dace.program
def sample_program(a: dace.float32[10], b: dace.float32[10], c: dace.float32[10]):
    for i in range(10):
        if a[i] > b[i]:
            c[i] = a[i] - b[i]
        else:
            c[i] = a[i] + b[i]
    c[:] = c[:] * 2.0


def _tasklet2p3g(
    sdfg_tasklet: Tasklet,
    builder: GraphBuilder,
    data_nodes: dict,
    symbols: dict,
    parent: SDFGState,
    analysis_only: bool = False,
) -> tuple[set, set]:
    reads = set()
    writes = set()

    for pred in parent.predecessors(sdfg_tasklet):
        for edge in parent.edges_between(pred, sdfg_tasklet):
            p3g_data_node = data_nodes[edge.data.data]
            subset = edge.data.src_subset
            reads.add((p3g_data_node, Int(0)))

    for succ in parent.successors(sdfg_tasklet):
        for edge in parent.edges_between(sdfg_tasklet, succ):
            p3g_data_node = data_nodes[edge.data.data]
            subset = edge.data.dst_subset
            reads.add((p3g_data_node, Int(0)))
            writes.add((p3g_data_node, Int(0)))

    if not analysis_only:
        builder.add_compute(sdfg_tasklet.label, list(reads), list(writes))
    return reads, writes


def _map2p3g(
    sdfg_map: MapEntry,
    builder: GraphBuilder,
    data_nodes: dict,
    symbols: dict,
    parent: SDFGState,
    analysis_only: bool = False,
) -> tuple[set, set]:
    reads = set()
    writes = set()

    map_exit = parent.exit_node(sdfg_map)

    for pred in parent.predecessors(sdfg_map):
        for edge in parent.edges_between(pred, sdfg_map):
            p3g_data_node = data_nodes[edge.data.data]
            subset = edge.data.src_subset
            reads.add((p3g_data_node, Int(0)))

    for succ in parent.successors(map_exit):
        for edge in parent.edges_between(map_exit, succ):
            p3g_data_node = data_nodes[edge.data.data]
            subset = edge.data.dst_subset
            reads.add((p3g_data_node, Int(0)))
            writes.add((p3g_data_node, Int(0)))

    if not analysis_only:
        iter_var = sdfg_map.map.params[0]
        map_init = sdfg_map.map.range.ranges[0][0]
        map_end = sdfg_map.map.range.ranges[0][1]

        with builder.add_map(
            sdfg_map.map.label,
            str(iter_var),
            str(map_init),
            str(map_end),
            reads=list(reads),
            writes=list(writes),
        ) as p3gmap:
            for node in dfs_topological_sort(
                parent.scope_subgraph(sdfg_map, include_entry=False, include_exit=False)
            ):
                if isinstance(node, AccessNode):
                    continue
                elif isinstance(node, Tasklet):
                    _tasklet2p3g(node, builder, data_nodes, symbols, parent)
                elif isinstance(node, NestedSDFG):
                    _sdfg2p3g(node.sdfg, builder)
    return reads, writes


def _state2p3g(
    sdfg_state: SDFGState,
    builder: GraphBuilder,
    data_nodes: dict,
    symbols: dict,
    analysis_only: bool = False,
) -> tuple[set, set]:
    reads = set()
    writes = set()
    scope_dict = sdfg_state.scope_dict()
    for node in dfs_topological_sort(sdfg_state):
        if scope_dict[node] is not None:
            continue
        if isinstance(node, AccessNode):
            continue
        elif isinstance(node, Tasklet):
            r, w = _tasklet2p3g(
                node, builder, data_nodes, symbols, sdfg_state, analysis_only
            )
        elif isinstance(node, MapEntry):
            r, w = _map2p3g(
                node, builder, data_nodes, symbols, sdfg_state, analysis_only
            )
        elif isinstance(node, NestedSDFG):
            r, w = _sdfg2p3g(node.sdfg, builder, analysis_only)
        reads.update(r)
        writes.update(w)
    return reads, writes


def _loop2p3g(
    sdfg_loop: LoopRegion,
    builder: GraphBuilder,
    data_nodes: dict,
    symbols: dict,
    analysis_only: bool = False,
) -> tuple[set, set]:
    reads = set()
    writes = set()
    for cfgs in dfs_topological_sort(sdfg_loop):
        if isinstance(cfgs, SDFGState):
            r, w = _state2p3g(cfgs, builder, data_nodes, symbols, analysis_only=True)
        elif isinstance(cfgs, LoopRegion):
            r, w = _loop2p3g(cfgs, builder, data_nodes, symbols, analysis_only=True)
        elif isinstance(cfgs, ConditionalBlock):
            r, w = _cond2p3g(cfgs, builder, data_nodes, symbols, analysis_only=True)
        reads.update(r)
        writes.update(w)

    if not analysis_only:
        iter_var = sdfg_loop.loop_variable
        loop_init = get_init_assignment(sdfg_loop)
        loop_end = get_loop_end(sdfg_loop)
        loop_stride = get_loop_stride(sdfg_loop)

        # Sanity check
        assert loop_stride == 1, "Only stride-1 loops are supported in P3G conversion."
        assert loop_init is not None and loop_end is not None, (
            "Loop bounds could not be determined."
        )

        with builder.add_loop(
            sdfg_loop.label,
            str(iter_var),
            str(loop_init),
            str(loop_end),
            reads=list(reads),
            writes=list(writes),
        ) as loop:
            if isinstance(cfgs, SDFGState):
                _state2p3g(cfgs, builder, data_nodes, symbols)
            elif isinstance(cfgs, LoopRegion):
                _loop2p3g(cfgs, builder, data_nodes, symbols)
            elif isinstance(cfgs, ConditionalBlock):
                _cond2p3g(cfgs, builder, data_nodes, symbols)
    return reads, writes


def _cond2p3g(
    sdfg_cond: ConditionalBlock,
    builder: GraphBuilder,
    data_nodes: dict,
    symbols: dict,
    analysis_only: bool = False,
) -> tuple[set, set]:
    tot_reads = set()
    tot_writes = set()

    for cond, branch in sdfg_cond.branches:
        branch_reads = set()
        branch_writes = set()
        # FIXME: What if the condition reads data?
        for cfgs in dfs_topological_sort(branch):
            if isinstance(cfgs, SDFGState):
                r, w = _state2p3g(
                    cfgs, builder, data_nodes, symbols, analysis_only=True
                )
            elif isinstance(cfgs, LoopRegion):
                r, w = _loop2p3g(cfgs, builder, data_nodes, symbols, analysis_only=True)
            elif isinstance(cfgs, ConditionalBlock):
                r, w = _cond2p3g(cfgs, builder, data_nodes, symbols, analysis_only=True)
            branch_reads.update(r)
            branch_writes.update(w)
        tot_reads.update(branch_reads)
        tot_writes.update(branch_writes)

    if not analysis_only:
        with builder.add_branch(
            sdfg_cond.label,
            reads=list(tot_reads),
            writes=list(tot_writes),
        ) as p3gbranch:
            for cond, branch in sdfg_cond.branches:
                with p3gbranch.add_path(str(cond)):
                    for cfgs in dfs_topological_sort(branch):
                        if isinstance(cfgs, SDFGState):
                            _state2p3g(cfgs, builder, data_nodes, symbols)
                        elif isinstance(cfgs, LoopRegion):
                            _loop2p3g(cfgs, builder, data_nodes, symbols)
                        elif isinstance(cfgs, ConditionalBlock):
                            _cond2p3g(cfgs, builder, data_nodes, symbols)

    return tot_reads, tot_writes


def _sdfg2p3g(
    sdfg: SDFG, builder: GraphBuilder, analysis_only: bool = False
) -> tuple[set, set]:
    # Add all symbols
    symbols = {}
    for sym, dtype in sdfg.symbols.items():
        p3g_sym = builder.add_symbol(sym)
        symbols[sym] = p3g_sym

    # Add all data descriptors
    data_nodes = {}
    for data_name, data_desc in sdfg.arrays.items():
        dnode = builder.add_data(data_name)
        data_nodes[data_name] = dnode

    # Traverse the SDFG and build the P3G
    reads = set()
    writes = set()
    for cfgs in dfs_topological_sort(sdfg):
        if isinstance(cfgs, SDFGState):
            r, w = _state2p3g(cfgs, builder, data_nodes, symbols, analysis_only)
        elif isinstance(cfgs, LoopRegion):
            r, w = _loop2p3g(cfgs, builder, data_nodes, symbols, analysis_only)
        elif isinstance(cfgs, ConditionalBlock):
            r, w = _cond2p3g(cfgs, builder, data_nodes, symbols, analysis_only)
        reads.update(r)
        writes.update(w)
    return reads, writes


def sdfg2p3g(sdfg: SDFG) -> Graph:
    builder = GraphBuilder()
    _sdfg2p3g(sdfg, builder)
    return builder.root_graph


if __name__ == "__main__":
    # if len(sys.argv) != 3:
    #     print("Usage: from_sdfg.py <input-sdfg> <output-p3g>")
    #     sys.exit(1)

    # input_sdfg_path = sys.argv[1]
    # output_p3g_path = sys.argv[2]

    # sdfg = dace.sdfg.SDFG.from_file(input_sdfg_path)
    sdfg = sample_program.to_sdfg()
    p3g = sdfg2p3g(sdfg)

    print_p3g_structure(p3g)
