"""
This module provides the P3GConverter class, which translates DaCe's SDFG (Stateful Dataflow Graph)
representation into a P3G (Program Property Graph) representation.
The P3G representation is designed to simplify dataflow and control flow analysis,
especially for symbolic memory access and data dependency analysis using SMT solvers.

The conversion process involves:
1. Initializing P3G symbols and data nodes from the SDFG's symbols and arrays.
2. Converting SymPy expressions and SDFG memory access ranges into PySMT formulas and coordinate sets.
3. Recursively traversing the SDFG structure (states, tasklets, maps, loops, conditionals, nested SDFGs).
4. For each SDFG construct, identifying data accesses (reads and writes) and representing them
   within the P3G using a GraphBuilder.
5. Establishing dataflow edges between P3G Data nodes based on SDFG memlets.
"""

import dace.symbolic as dsym
import sympy as sp
from dace.sdfg import SDFG
from dace.sdfg.nodes import AccessNode, Tasklet, MapEntry, NestedSDFG
from dace.sdfg.state import LoopRegion, SDFGState, ConditionalBlock
from dace.sdfg.utils import dfs_topological_sort
from dace.transformation.passes.analysis.loop_analysis import (
    get_loop_end,
    get_init_assignment,
    get_loop_stride,
)
from plum import dispatch
from pysmt.shortcuts import (
    GE,
    LE,
    Plus,
    Int,
    Times,
    GT,
    LT,
    Equals,
)

from p3g.graph import Graph, GraphBuilder, PysmtRange, PysmtCoordSet, Data
from p3g.subsets import PysmtFormula, PysmtSymbol

DataSubset = set[tuple[Data, PysmtCoordSet]]
AnalyzedAccess = set[tuple[str, PysmtCoordSet]]


def _symexpr_to_pysmt(
    expr: sp.Expr, symbols: dict[str, PysmtSymbol], current_sdfg: SDFG
) -> PysmtFormula:
    """
    Converts a SymPy expression (used in SDFG) into a PySMT formula.

    This method handles basic arithmetic operations, relational operators,
    and resolves SDFG symbols to their P3G PysmtSymbol equivalents or
    concrete integer values if they are constants.

    Args:
        expr: The SymPy expression to convert.
        current_sdfg: The current SDFG context for symbol resolution.

    Returns:
        A PysmtFormula representing the converted SymPy expression.

    Raises:
        NotImplementedError: If the expression type cannot be converted.
    """
    # If the expression is a symbol already tracked by P3G, return its PysmtSymbol.
    if str(expr) in symbols:
        return symbols[str(expr)]

    # Attempt to resolve the symbol to a constant value within the SDFG context.
    resolved = dsym.resolve_symbol_to_constant(expr, current_sdfg)
    if resolved is not None:
        return Int(int(resolved))

    # Recursively walk through the SymPy expression tree for conversion.
    if expr.is_Add:
        args = expr.as_ordered_terms()
        pysmt_args = [_symexpr_to_pysmt(arg, symbols, current_sdfg) for arg in args]
        return Plus(pysmt_args)
    elif expr.is_Mul:
        args = expr.as_ordered_factors()
        pysmt_args = [_symexpr_to_pysmt(arg, symbols, current_sdfg) for arg in args]
        return Times(pysmt_args)
    elif expr.is_Relational:
        left = _symexpr_to_pysmt(expr.lhs, symbols, current_sdfg)
        right = _symexpr_to_pysmt(expr.rhs, symbols, current_sdfg)
        if expr.rel_op == ">=":
            return GE(left, right)
        elif expr.rel_op == "<=":
            return LE(left, right)
        elif expr.rel_op == ">":
            return GT(left, right)
        elif expr.rel_op == "<":
            return LT(left, right)
        elif expr.rel_op == "==":
            return Equals(left, right)

    raise NotImplementedError(f"Expression {expr} could not be converted to Pysmt.")


def _ranges_to_pysmt(
    ranges: list[tuple[sp.Expr, sp.Expr, sp.Expr]],
    symbols: dict[str, PysmtSymbol],
    current_sdfg: SDFG,
) -> PysmtCoordSet:
    """
    Converts a list of SDFG ranges (e.g., from memlets) into a PysmtCoordSet.

    Each SDFG range `(start, end, stride)` is converted into a PysmtRange,
    and these are aggregated into a PysmtCoordSet.

    Args:
        ranges: A list of SDFG range tuples (start, end, stride).
        current_sdfg: The current SDFG context for symbol resolution within range expressions.

    Returns:
        A PysmtCoordSet representing the collection of converted ranges.
    """
    pysmt_ranges = []
    for r in ranges:
        start_expr = _symexpr_to_pysmt(r[0], symbols, current_sdfg)
        end_expr = _symexpr_to_pysmt(r[1], symbols, current_sdfg)
        pysmt_ranges.append(PysmtRange(start_expr, end_expr))
    return PysmtCoordSet(*pysmt_ranges)


class SDFGAccessAnalyzer:
    """
    Analyzes an SDFG subgraph to determine data accesses (reads and writes)
    without creating P3G nodes. It provides a pure analysis of SDFG structure.
    """

    def __init__(self, symbols: dict[str, PysmtSymbol]):
        self.symbols = symbols

    @dispatch
    def _get_node_accesses(
        self, tasklet: Tasklet, parent_state: SDFGState
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """
        Determines the data reads and writes for a Tasklet node.
        """
        reads, writes = set(), set()
        for edge in parent_state.in_edges(tasklet):
            rname = edge.src.data
            rset = _ranges_to_pysmt(
                edge.data.src_subset.ranges, self.symbols, parent_state.sdfg
            )
            reads.add((rname, rset))

        for edge in parent_state.out_edges(tasklet):
            wname = edge.dst.data
            wset = _ranges_to_pysmt(
                edge.data.dst_subset.ranges, self.symbols, parent_state.sdfg
            )
            writes.add((wname, wset))
            reads.add((wname, wset))
        return reads, writes

    @dispatch
    def _get_node_accesses(
        self, access: AccessNode, parent_state: SDFGState
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """
        AccessNodes are data containers; accesses are handled by connected nodes.
        """
        reads, writes = set(), set()
        for edge in parent_state.in_edges(access):
            if isinstance(edge.src, AccessNode):
                rname = edge.src.data
                rset = _ranges_to_pysmt(
                    edge.data.src_subset.ranges, self.symbols, parent_state.sdfg
                )
                reads.add((rname, rset))
        for edge in parent_state.out_edges(access):
            if isinstance(edge.dst, AccessNode):
                wname = edge.dst.data
                wset = _ranges_to_pysmt(
                    edge.data.dst_subset.ranges, self.symbols, parent_state.sdfg
                )
                writes.add((wname, wset))
                reads.add((wname, wset))
        return reads, writes

    @dispatch
    def _get_node_accesses(
        self, mapentry: MapEntry, parent_state: SDFGState
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """
        Determines the data reads and writes for a Map's boundary.
        """
        reads, writes = set(), set()
        map_exit = parent_state.exit_node(mapentry)

        for pred in parent_state.predecessors(mapentry):
            for edge in parent_state.edges_between(pred, mapentry):
                rname = edge.src.data
                rset = _ranges_to_pysmt(
                    edge.data.src_subset.ranges, self.symbols, parent_state.sdfg
                )
                reads.add((rname, rset))

        for succ in parent_state.successors(map_exit):
            for edge in parent_state.edges_between(map_exit, succ):
                wname = edge.dst.data
                wset = _ranges_to_pysmt(
                    edge.data.dst_subset.ranges, self.symbols, parent_state.sdfg
                )
                writes.add((wname, wset))
                reads.add((wname, wset))
        return reads, writes

    @dispatch
    def get_accesses(
        self, tasklet: Tasklet, parent_state: SDFGState | None
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """Gathers accesses for a Tasklet node."""
        assert parent_state is not None
        return self._get_node_accesses(tasklet, parent_state)

    @dispatch
    def get_accesses(
        self, access: AccessNode, parent_state: SDFGState | None
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """Gathers accesses for an AccessNode."""
        assert parent_state is not None
        return self._get_node_accesses(access, parent_state)

    @dispatch
    def get_accesses(
        self, mapentry: MapEntry, parent_state: SDFGState | None
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """Gathers accesses for a MapEntry node."""
        assert parent_state is not None
        return self._get_node_accesses(mapentry, parent_state)

    @dispatch
    def get_accesses(
        self, state: SDFGState, parent_state: SDFGState | None
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """Gathers accesses for an entire SDFGState by recurring."""
        return self.get_total_subgraph_accesses(dfs_topological_sort(state), state)

    @dispatch
    def get_accesses(
        self, loop: LoopRegion, parent_state: SDFGState | None
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """Gathers accesses for a LoopRegion by recurring."""
        return self.get_total_subgraph_accesses(
            dfs_topological_sort(loop), parent_state
        )

    @dispatch
    def get_accesses(
        self, condblock: ConditionalBlock, parent_state: SDFGState | None
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """Gathers accesses for a ConditionalBlock by summing up all branches."""
        cond_reads, cond_writes = set(), set()
        for _, branch_cfg in condblock.branches:
            branch_r, branch_w = self.get_total_subgraph_accesses(
                dfs_topological_sort(branch_cfg), parent_state
            )
            cond_reads.update(branch_r)
            cond_writes.update(branch_w)
        return cond_reads, cond_writes

    @dispatch
    def get_accesses(
        self, nestedsdfg: NestedSDFG, parent_state: SDFGState | None
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """Gathers accesses for a NestedSDFG by creating a new analyzer."""
        nested_symbols = {}
        for outer_sym, inner_sym in nestedsdfg.symbol_mapping.items():
            if outer_sym in self.symbols:
                nested_symbols[inner_sym] = self.symbols[outer_sym]

        nested_analyzer = SDFGAccessAnalyzer(nestedsdfg.sdfg, nested_symbols)

        inner_reads, inner_writes = nested_analyzer.get_accesses(nestedsdfg.sdfg, None)

        outer_reads = {
            (nestedsdfg.data_mapping[name], subset) for name, subset in inner_reads
        }
        outer_writes = {
            (nestedsdfg.data_mapping[name], subset) for name, subset in inner_writes
        }
        return outer_reads, outer_writes

    @dispatch
    def get_accesses(
        self, sdfg: SDFG, parent_state: SDFGState | None
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """Gathers accesses for an entire SDFG."""
        return self.get_total_subgraph_accesses(
            dfs_topological_sort(sdfg), parent_state
        )

    def get_total_subgraph_accesses(
        self, nodes, parent_state: SDFGState | None
    ) -> tuple[AnalyzedAccess, AnalyzedAccess]:
        """
        Aggregates all data reads and writes within a given subgraph.
        """
        total_reads, total_writes = set(), set()

        for n in nodes:
            r, w = self.get_accesses(n, parent_state)
            total_reads.update(r)
            total_writes.update(w)
        return total_reads, total_writes


class P3GConverter:
    """
    Converts a DaCe SDFG into a P3G (Program Property Graph) representation.

    The P3G is built using a GraphBuilder and is intended for symbolic analysis
    of data dependencies and memory access patterns. It translates SDFG components
    like states, tasklets, maps, loops, conditionals, and nested SDFGs into
    corresponding P3G constructs, representing memory accesses with PySMT formulas.
    """

    def __init__(self, sdfg: SDFG):
        """
        Initializes the P3GConverter with a given SDFG.

        Args:
            sdfg: The DaCe SDFG to convert.
        """
        self.builder = GraphBuilder()
        self.sdfg = sdfg

        # Which arrays are even there.
        self._declared_arrays: set[str] = set(
            name for name, _ in self.sdfg.arrays.items()
        )
        # TODO: A table of which arrays are transient proper.

        # Persistent arrays are considered output.
        self.output_data_names: set[str] = set(
            name for name, desc in self.sdfg.arrays.items() if not desc.transient
        )

        # Stores a mapping from SDFG symbol names to their P3G PysmtSymbol representations.
        self.symbols: dict[str, PysmtSymbol] = {}
        for sym_name, _ in self.sdfg.symbols.items():
            self.symbols[sym_name] = self.builder.add_symbol(sym_name)

        # Access analyzer
        self.access_analyzer = SDFGAccessAnalyzer(self.symbols)

        # Graph -> State -> Array -> Ref.
        self._array_state: dict[tuple[Graph, str, str], Data] = {}
        self._current_array_state_stack: list[str] = ["."]

    @dispatch
    def _convert_node(
        self, tasklet: Tasklet, parent_state: SDFGState
    ) -> tuple[DataSubset, DataSubset]:
        """
        Converts an SDFG Tasklet node into a P3G Compute node, using SSA-style data versioning.
        Reads are from the current live data versions, and writes create new live versions.
        """
        cstate = self._current_array_state_stack[-1]

        reads = []
        # Gather reads from current live versions
        for edge in parent_state.in_edges(tasklet):
            key = (self.builder.current_graph, cstate, edge.src.data)
            if key in self._array_state:
                rnode = self._array_state[key]
            else:
                rnode = self.builder.add_data(edge.src.data)
                self._array_state[key] = rnode
            rset = _ranges_to_pysmt(
                edge.data.src_subset.ranges, self.symbols, parent_state.sdfg
            )
            reads.append((rnode, rset))

        # Gather writes, creating new versions for each
        # A temporary dictionary to hold writes for this tasklet, in case it writes to the same array multiple times.
        writes = []
        writes_nus = {}
        for edge in parent_state.out_edges(tasklet):
            key = (self.builder.current_graph, cstate, edge.dst.data)
            if key in self._array_state:
                wnode = self._array_state[key]
            else:
                wnode = self.builder.add_data(edge.dst.data)
                self._array_state[key] = wnode
            wnode_nu = self.builder.add_data(edge.dst.data)
            wset = _ranges_to_pysmt(
                edge.data.dst_subset.ranges, self.symbols, parent_state.sdfg
            )
            reads.append((wnode, wset))
            writes.append((wnode_nu, wset))
            writes_nus[key] = wnode_nu
        self.builder.add_compute(tasklet.label, reads, writes)
        for k, wn in writes_nus.items():
            self._array_state[k] = wn

        return set(reads), set(writes)

    @dispatch
    def _convert_node(
        self, access: AccessNode, parent_state: SDFGState
    ) -> tuple[DataSubset, DataSubset]:
        """
        Converts an SDFG AccessNode. In the SSA model, an AccessNode represents
        a version change of the data. It creates a new live version of the
        data array and adds a P3G edge from the previous version to the new one.
        """
        assert len(parent_state.in_edges(access)) <= 1, (
            f"Cannot have many writes to an access node; got {parent_state.in_edges(access)}"
        )
        if not parent_state.in_edges(access):
            return set(), set()

        (wedge,) = parent_state.in_edges(access)
        if not isinstance(wedge.src, AccessNode):
            return set(), set()

        cstate = self._current_array_state_stack[-1]
        rset = _ranges_to_pysmt(
            wedge.data.src_subset.ranges, self.symbols, parent_state.sdfg
        )
        wset = _ranges_to_pysmt(
            wedge.data.dst_subset.ranges, self.symbols, parent_state.sdfg
        )
        key = (self.builder.current_graph, cstate, wedge.src.data)
        if key in self._array_state:
            rnode = self._array_state[key]
        else:
            rnode = self.builder.add_data(wedge.src.data)
            self._array_state[key] = rnode
        key = (self.builder.current_graph, cstate, wedge.dst.data)
        if key in self._array_state:
            wnode = self._array_state[key]
        else:
            wnode = self.builder.add_data(wedge.dst.data)
            self._array_state[key] = wnode
        wnode_nu = self.builder.add_data(wedge.dst.data)

        reads = {(rnode, rset), (wnode, wset)}
        writes = {(wnode_nu, wset)}
        self.builder.add_compute(
            "copy", [(rnode, rset), (wnode, wset)], [(wnode_nu, wset)]
        )
        return reads, writes

    @dispatch
    def _convert_node(
        self, mapentry: MapEntry, parent_state: SDFGState
    ) -> tuple[DataSubset, DataSubset]:
        """
        Converts an SDFG MapEntry node into a P3G Map construct.

        This method captures the iteration variable, its bounds, and recursively
        converts the nodes contained within the map's scope.

        Args:
            mapentry: The SDFG MapEntry node to convert.
            parent_state: The SDFGState containing the map entry.

        Returns:
            A tuple of sets representing the reads and writes associated with the map.
        """
        # First, determine the data accesses for the map's boundary (input/output memlets).
        reads, writes = self.access_analyzer.get_total_subgraph_accesses(mapentry, None)
        p3g_writes = [
            (self.builder.add_write_data(name), wset) for name, wset in writes
        ]
        p3g_reads = [
            (self.builder.add_read_data(name), rset) for name, rset in reads
        ] + [(r, wset) for (r, w), wset in p3g_writes]
        p3g_writes = [(w, wset) for (r, w), wset in p3g_writes]

        # Extract map iteration variable and its initial/final values.
        iter_var = mapentry.map.params[0]
        # Assuming single-dimensional map for now; access the first range.
        map_init_raw, map_end_raw, _ = mapentry.map.range.ranges[0]

        # Add the iteration variable as a new symbol in the P3G builder's current scope.
        pysmt_iter_var = self.builder.add_symbol(str(iter_var))
        # Convert map bounds to PySMT formulas.
        pysmt_map_init = _symexpr_to_pysmt(
            map_init_raw, self.symbols, parent_state.sdfg
        )
        pysmt_map_end = _symexpr_to_pysmt(map_end_raw, self.symbols, parent_state.sdfg)

        # Add the map construct to the P3G builder.
        # The 'with' statement ensures proper scope handling for nested elements.
        with self.builder.add_map(
            mapentry.map.label,
            str(iter_var),
            pysmt_map_init,
            pysmt_map_end,
            reads=p3g_reads,
            writes=p3g_writes,
        ) as p3gmap:
            # Recursively convert all nodes within the map's scope.
            for node in dfs_topological_sort(
                parent_state.scope_subgraph(
                    mapentry, include_entry=False, include_exit=False
                )
            ):
                self._convert_node(node, parent_state)

        return set(p3g_reads), set(p3g_writes)

    @dispatch
    def _convert_node(
        self, nestedsdfg: NestedSDFG, parent_state: SDFGState
    ) -> tuple[DataSubset, DataSubset]:
        """
        Converts an SDFG NestedSDFG node into a P3G Compute node.

        The nested SDFG is fully converted internally, and its aggregated
        reads and writes are used to represent it as a single compute unit
        in the parent P3G.

        Args:
            nestedsdfg: The SDFG NestedSDFG node to convert.
            parent_state: The SDFGState containing the nested SDFG.

        Returns:
            A tuple of sets representing the total reads and writes of the nested SDFG.
        """
        # Create a new P3GConverter instance specifically for the nested SDFG.
        nested_converter = P3GConverter(nestedsdfg.sdfg)

        # Convert the nested SDFG entirely using its own converter.
        # This returns the top-level reads and writes of the nested SDFG.
        nested_sdfg_reads, nested_sdfg_writes = nested_converter._convert_node(
            nestedsdfg.sdfg, None
        )

        # Represent the entire NestedSDFG as a single Compute node in the parent's P3G.
        self.builder.add_compute(
            nestedsdfg.label, list(nested_sdfg_reads), list(nested_sdfg_writes)
        )
        return nested_sdfg_reads, nested_sdfg_writes

    @dispatch
    def _convert_node(
        self, state: SDFGState, parent_state: SDFGState | None
    ) -> tuple[DataSubset, DataSubset]:
        """
        Converts an SDFGState by processing its contained nodes.

        This method iterates through the nodes within an SDFGState that are
        not part of a nested scope (e.g., maps, loops, conditionals) and
        dispatches their conversion to appropriate `_convert_node` methods.

        Args:
            state: The SDFGState to convert.
            parent_state: Always None for a top-level state conversion.

        Returns:
            A tuple of sets representing the aggregated reads and writes within the state.
        """
        reads, writes = set(), set()
        # Get the scope dictionary to identify nodes not part of a nested scope.
        scope_dict = state.scope_dict()

        # Iterate through nodes in topological order.
        for node in dfs_topological_sort(state):
            # Only process nodes that are not within a map scope (scope_dict[node] is None).
            if scope_dict[node] is not None:
                continue

            # Dispatch conversion to the appropriate _convert_node method.
            r, w = self._convert_node(node, state)
            reads.update(r)
            writes.update(w)
        return reads, writes

    @dispatch
    def _convert_node(
        self, loop: LoopRegion, parent_state: SDFGState | None
    ) -> tuple[DataSubset, DataSubset]:
        """
        Converts an SDFG LoopRegion into a P3G Loop construct.

        This method extracts loop variables and bounds, aggregates data accesses
        for the entire loop body, and recursively converts the CFG nodes within the loop.

        Args:
            loop: The SDFG LoopRegion to convert.
            parent_state: The SDFGState that contains this loop region in the CFG, or None if it's a top-level CFG node.

        Returns:
            A tuple of sets representing the aggregated reads and writes of the loop.

        Raises:
            AssertionError: If the loop stride is not 1 or loop bounds cannot be determined.
        """
        reads, writes = self.access_analyzer.get_total_subgraph_accesses(loop, None)
        p3g_writes = [
            (self.builder.add_write_data(name), wset) for name, wset in writes
        ]
        p3g_reads = [
            (self.builder.add_read_data(name), rset) for name, rset in reads
        ] + [(r, wset) for (r, w), wset in p3g_writes]
        p3g_writes = [(w, wset) for (r, w), wset in p3g_writes]

        # Extract loop iteration variable and bounds.
        iter_var = loop.loop_variable
        loop_init = get_init_assignment(loop)
        loop_end = get_loop_end(loop)
        loop_stride = get_loop_stride(loop)

        # Sanity checks for supported loop types.
        assert loop_stride == 1, "Only stride-1 loops are supported in P3G conversion."
        assert loop_init is not None and loop_end is not None, (
            "Loop bounds could not be determined."
        )

        # Add the loop iteration variable as a new symbol to the current P3G scope.
        self.builder.add_symbol(str(iter_var))
        # Convert loop bounds to PySMT formulas.
        pysmt_loop_init = _symexpr_to_pysmt(loop_init, self.symbols, self.sdfg)
        pysmt_loop_end = _symexpr_to_pysmt(loop_end, self.symbols, self.sdfg)

        # Add the loop construct to the P3G builder.
        with self.builder.add_loop(
            loop.label,
            str(iter_var),
            pysmt_loop_init,
            pysmt_loop_end,
            reads=p3g_reads,
            writes=p3g_writes,
        ) as p3gloop:
            self._current_array_state_stack.append(".")
            # Recursively convert all CFG nodes within the loop body.
            # Pass the parent_state of the LoopRegion itself as the parent context.
            for cfg_node in dfs_topological_sort(loop):
                self._convert_node(cfg_node, parent_state)
            self._current_array_state_stack.pop()

        return set(p3g_reads), set(p3g_writes)

    @dispatch
    def _convert_node(
        self, sdfg_cond: ConditionalBlock, parent_state: SDFGState | None
    ) -> tuple[DataSubset, DataSubset]:
        """
        Converts an SDFG ConditionalBlock into a P3G Branch construct.

        This method aggregates data accesses across all branches of the conditional
        and then recursively converts the CFG nodes within each branch,
        associating them with their respective conditions.

        Args:
            sdfg_cond: The SDFG ConditionalBlock to convert.
            parent_state: Always None for a top-level conditional block conversion.

        Returns:
            A tuple of sets representing the aggregated reads and writes across all branches.

        Raises:
            AssertionError: If multiple 'else' branches are found or an 'else' branch is not last.
        """
        # Get the actual SDFGState that contains this conditional block.
        parent_state = sdfg_cond.sdfg.node(sdfg_cond.state_id)

        # Collect all data reads and writes that occur across all branches of the conditional block.
        total_reads = set()
        total_writes = set()
        for cond_expr, branch_cfg in sdfg_cond.branches:
            branch_r, branch_w = self._get_total_subgraph_accesses(
                dfs_topological_sort(branch_cfg), parent_state
            )
            total_reads.update(branch_r)
            total_writes.update(branch_w)

        # Add the branch construct to the P3G builder.
        with self.builder.add_branch(
            sdfg_cond.label,
            reads=list(total_reads),
            writes=list(total_writes),
        ) as p3gbranch:
            else_handled = False
            # sympy.true is used to accumulate conditions for the implicit 'else' branch.
            symexpr_combined = sp.true
            for cond_expr, branch_cfg in sdfg_cond.branches:
                # Determine the condition for the current branch path.
                if cond_expr is None:  # This indicates the 'else' branch.
                    assert not else_handled, (
                        "Multiple 'else' branches found in ConditionalBlock."
                    )
                    # The 'else' condition is the negation of all previous conditions combined.
                    ast_condition = _symexpr_to_pysmt(
                        sp.Not(symexpr_combined), self.symbols, self.sdfg
                    )
                    else_handled = True
                else:
                    assert not else_handled, (
                        "'else' branch must be last in ConditionalBlock."
                    )
                    # Convert the string condition to a SymPy expression.
                    symexpr = dsym.pystr_to_symbolic(cond_expr.as_string)
                    # Accumulate conditions for the eventual 'else' branch.
                    symexpr_combined = sp.And(symexpr_combined, symexpr)
                    # Convert the current branch condition to PySMT.
                    ast_condition = _symexpr_to_pysmt(
                        symexpr, self.symbols, self.symbols, self.sdfg
                    )

                # Add a path to the P3G branch construct with its condition.
                with p3gbranch.add_path(ast_condition):
                    # Recursively convert all nodes within this branch's CFG.
                    for node_or_cfg in dfs_topological_sort(branch_cfg):
                        self._convert_node(node_or_cfg, parent_state)

        return total_reads, total_writes

    @dispatch
    def _convert_node(
        self, sdfg: SDFG, parent_state: SDFGState | None
    ) -> tuple[DataSubset, DataSubset]:
        """
        Orchestrates the main conversion process of an SDFG to P3G.

        This method traverses the top-level CFG nodes of the SDFG (states, loops, conditionals)
        in topological order and dispatches their conversion to the appropriate
        `_convert_node` methods.

        Args:
            sdfg: The SDFG to convert.

        Returns:
            A tuple of sets representing the aggregated reads and writes of the entire SDFG.
        """
        reads, writes = set(), set()
        # Iterate through the top-level CFG nodes (e.g., SDFGStates) of the SDFG.
        for cfgs in dfs_topological_sort(sdfg):
            # Dispatch to the appropriate _convert_node method for the current CFG node.
            # For top-level CFG nodes, the parent_state is None.
            r, w = self._convert_node(cfgs, None)
            reads.update(r)
            writes.update(w)
        return reads, writes

    def convert(self) -> "Graph":
        """
        Initiates the conversion of the SDFG (provided during initialization)
        into a P3G Graph representation.

        This is the primary public API for performing the conversion.

        Returns:
            The root P3G Graph object.
        """
        # Call the internal _convert_sdfg method with the SDFG provided at initialization.
        self._convert_node(self.sdfg, None)
        # Return the constructed P3G Graph from the builder.
        return self.builder.root_graph
