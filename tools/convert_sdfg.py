"""
This file converts a DaCe SDFG into a P3G Graph representation.

Some notes:
- We likely need a preprocessing pass
- What if nested SDFGs have symbols that shadow parent SDFG symbols (and array names)?
- What about symbol updates on interstate edges? (and arrays?)
- What about array access in condition expressions or loop bounds?

"""

import dace
import sys
import os
import argparse
from dace.sdfg import SDFG
from dace.sdfg.utils import dfs_topological_sort
from dace.transformation.passes.analysis.loop_analysis import (
    get_loop_end,
    get_init_assignment,
    get_loop_stride,
)
from dace.sdfg.nodes import AccessNode, Tasklet, MapEntry, MapExit, NestedSDFG
from dace.sdfg.state import LoopRegion, SDFGState, ConditionalBlock
import dace.symbolic as dsym
import sympy as sp
from z3 import *

from pysmt.shortcuts import (
    Symbol,
    INT,
    TRUE,
    And,
    GE,
    LE,
    Plus,
    Int,
    simplify,
    Times,
    GT,
    LT,
    Equals,
)

# Add the project root to the sys.path
script_dir = os.path.dirname(__file__)
project_root = os.path.abspath(os.path.join(script_dir, os.pardir))
sys.path.insert(0, project_root)

from p3g.graph import GraphBuilder, Graph, Loop, PysmtRange, PysmtCoordSet
from p3g.smt import exists_data_forall_bounds_forall_iter_isdep
from tests.utils import print_p3g_structure

N = dace.symbol("N", dace.int32)


@dace.program
def sample_program(
    a: dace.float32[N + 1], b: dace.float32[N + 1], c: dace.float32[N + 1]
):
    for i in range(N + 1):
        if a[i] > b[i]:
            c[i] = a[i] - b[i]
        else:
            c[i] = a[i] + b[i]
    # c[:] = c[:] * 2.0


def _symexpr_to_pysmt(expr, symbols, sdfg):
    if str(expr) in symbols:
        return symbols[str(expr)]

    resolved = dsym.resolve_symbol_to_constant(expr, sdfg)
    if resolved is not None:
        return Int(int(resolved))

    # Walk through the sympy expression
    if expr.is_Add:
        args = expr.as_ordered_terms()
        pysmt_args = [_symexpr_to_pysmt(arg, symbols, sdfg) for arg in args]
        return Plus(pysmt_args)
    elif expr.is_Mul:
        args = expr.as_ordered_factors()
        pysmt_args = [_symexpr_to_pysmt(arg, symbols, sdfg) for arg in args]
        return Times(pysmt_args)
    elif expr.is_Relational:
        left = _symexpr_to_pysmt(expr.lhs, symbols, sdfg)
        right = _symexpr_to_pysmt(expr.rhs, symbols, sdfg)
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


def _ranges_to_pysmt(ranges, symbols, sdfg):
    pysmt_ranges = []
    for r in ranges:
        start = _symexpr_to_pysmt(r[0], symbols, sdfg)
        end = _symexpr_to_pysmt(r[1], symbols, sdfg)
        pysmt_ranges.append(PysmtRange(start, end))
    return PysmtCoordSet(*pysmt_ranges)


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
            ranges = edge.data.src_subset.ranges
            converted = _ranges_to_pysmt(
                ranges,
                symbols,
                parent.sdfg,
            )
            reads.add((p3g_data_node, converted))

    for succ in parent.successors(sdfg_tasklet):
        for edge in parent.edges_between(sdfg_tasklet, succ):
            p3g_data_node = data_nodes[edge.data.data]
            ranges = edge.data.dst_subset.ranges
            converted = _ranges_to_pysmt(
                ranges,
                symbols,
                parent.sdfg,
            )
            reads.add((p3g_data_node, converted))
            writes.add((p3g_data_node, converted))

    if not analysis_only:
        builder.add_compute(sdfg_tasklet.label, list(reads), list(writes))
    return reads, writes


def _accessnode2p3g(
    sdfg_access: AccessNode,
    builder: GraphBuilder,
    data_nodes: dict,
    symbols: dict,
    parent: SDFGState,
    analysis_only: bool = False,
) -> tuple[set, set]:
    reads = set()
    writes = set()

    for pred in parent.predecessors(sdfg_access):
        for edge in parent.edges_between(pred, sdfg_access):
            if edge.data.src_subset is None:
                continue
            p3g_data_node = data_nodes[edge.data.data]
            ranges = edge.data.src_subset.ranges
            converted = _ranges_to_pysmt(
                ranges,
                symbols,
                parent.sdfg,
            )
            reads.add((p3g_data_node, converted))

            if not analysis_only:
                builder.add_edge(p3g_data_node, data_nodes[sdfg_access.data], converted)

    for succ in parent.successors(sdfg_access):
        for edge in parent.edges_between(sdfg_access, succ):
            if edge.data.dst_subset is None:
                continue
            p3g_data_node = data_nodes[edge.data.data]
            ranges = edge.data.dst_subset.ranges
            converted = _ranges_to_pysmt(
                ranges,
                symbols,
                parent.sdfg,
            )
            reads.add((p3g_data_node, converted))
            writes.add((p3g_data_node, converted))

            if not analysis_only:
                builder.add_edge(data_nodes[sdfg_access.data], p3g_data_node, converted)

    return reads, writes


# TODO: Support reduction
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

    for sym in sdfg_map.map.params:
        if str(sym) not in symbols:
            p3g_sym = builder.add_symbol(str(sym))
            symbols[str(sym)] = p3g_sym
    map_exit = parent.exit_node(sdfg_map)

    for pred in parent.predecessors(sdfg_map):
        for edge in parent.edges_between(pred, sdfg_map):
            p3g_data_node = data_nodes[edge.data.data]
            ranges = edge.data.src_subset.ranges
            converted = _ranges_to_pysmt(
                ranges,
                symbols,
                parent.sdfg,
            )
            reads.add((p3g_data_node, converted))

    for succ in parent.successors(map_exit):
        for edge in parent.edges_between(map_exit, succ):
            p3g_data_node = data_nodes[edge.data.data]
            ranges = edge.data.dst_subset.ranges
            converted = _ranges_to_pysmt(
                ranges,
                symbols,
                parent.sdfg,
            )
            reads.add((p3g_data_node, converted))
            writes.add((p3g_data_node, converted))

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
                    _accessnode2p3g(node, builder, data_nodes, symbols, parent)
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
            r, w = _accessnode2p3g(
                node, builder, data_nodes, symbols, sdfg_state, analysis_only
            )
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

        iter_var = str(iter_var)
        loop_init = _symexpr_to_pysmt(loop_init, symbols, sdfg_loop.sdfg)
        loop_end = _symexpr_to_pysmt(loop_end, symbols, sdfg_loop.sdfg)

        with builder.add_loop(
            sdfg_loop.label,
            iter_var,
            loop_init,
            loop_end,
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
            else_handled = False
            symexpr_combined = sp.true
            for cond, branch in sdfg_cond.branches:
                if cond is None:
                    assert not else_handled, (
                        "Multiple 'else' branches found in ConditionalBlock."
                    )
                    ast = _symexpr_to_pysmt(
                        sp.Not(symexpr_combined), symbols, sdfg_cond.sdfg
                    )
                    else_handled = True
                else:
                    assert not else_handled, (
                        "'else' branch must be last in ConditionalBlock."
                    )
                    symexpr = dsym.pystr_to_symbolic(cond.as_string)
                    symexpr_combined = sp.And(symexpr_combined, symexpr)
                    ast = _symexpr_to_pysmt(symexpr, symbols, sdfg_cond.sdfg)

                with p3gbranch.add_path(ast):
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

    for argname, argtype in sdfg.arglist().items():
        builder.mark_array_as_output(argname)

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
    parser = argparse.ArgumentParser(description="Convert a DaCe SDFG to a P3G graph.")
    parser.add_argument("-i", "--input", required=False, help="Input SDFG file path.")
    parser.add_argument(
        "-p3g",
        "--dump-p3g",
        required=False,
        help="Output the P3G structure.",
        action=argparse.BooleanOptionalAction,
    )
    parser.add_argument(
        "-smt",
        "--dump-smt",
        required=False,
        help="Output the SMT for the top-level loop.",
        action=argparse.BooleanOptionalAction,
    )
    parser.add_argument(
        "-s",
        "--solve",
        required=False,
        help="Solve the SMT using Z3.",
        action=argparse.BooleanOptionalAction,
    )
    args = parser.parse_args()

    # If the user provided an input SDFG file, load it; otherwise, use the sample program.
    if args.input:
        sdfg = dace.sdfg.SDFG.from_file(args.input)
    else:
        sdfg = sample_program.to_sdfg()

    # Convert SDFG to P3G
    p3g = sdfg2p3g(sdfg)

    # Generate the SMT
    loops = tuple(n for n in p3g.nodes if isinstance(n, Loop))
    assert len(loops) == 1
    (loop,) = loops
    smt = exists_data_forall_bounds_forall_iter_isdep(loop, verbose=False)

    # If the user requested, dump the P3G structure
    if args.dump_p3g:
        print_p3g_structure(p3g)

    # Optionally dump the SMT
    if args.dump_smt:
        print(smt)

    # Optionally solve the SMT
    if args.solve:
        solver = Solver()
        solver.from_string(smt)
        if solver.check() == sat:
            print("SMT is SAT")
        else:
            print("SMT is UNSAT")
