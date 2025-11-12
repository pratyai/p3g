from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.shortcuts import Symbol, INT, ArrayType, Int, Select

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_indirect_write_scatter():
    """
    Test case for Indirect Write (Scatter) operation: for i = 1...N: A[ IDX[i] ] = B[i].
    This operation is generally sequential because multiple iterations can write to the same
    memory location in A if IDX[i] values are not unique or create dependencies.
    For example, if IDX[i] = 5 for all i, then all iterations write to A[5], creating a WAW dependency.
    However, the SMT query is designed to prove *existence* of a sequentializing data configuration.
    If the loop is *always* sequential (DOFS), the SMT solver should return SAT.
    If the loop is *not always* sequential (Not DOFS / Parallelizable), the SMT solver should return UNSAT.

    The current test expects the loop to be Not DOFS (parallelizable) for *some* data configurations,
    meaning it's not *always* sequential. This implies the SMT solver should return UNSAT.
    """
    print(
        "\n--- Running Test: Indirect Write (Scatter) (Expected: Not DOFS/Parallel) ---"
    )
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")
    IDX_val = Symbol("IDX_val", ArrayType(INT, INT))
    IDX_root = b.add_data("IDX", pysmt_array_sym=IDX_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[(B_root, (Int(0), N)), (IDX_root, (Int(0), N))],
        writes=[(A_root, (Int(0), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        IDX_local = b.add_data("IDX")

        write_idx = Select(IDX_val, k)

        b.add_compute(
            "T1_scatter",
            reads=[(B_local, k), (IDX_local, k)],
            writes=[(A_local, write_idx)],
        )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    print(f"Generating SMT query for N (symbolic).")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, verbose=False
    )
    print("\n--- Generated SMT Query (indirect_write_scatter) ---")
    print(smt_query)
    print("---------------------------------------------------")

    # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
    # across *all* adjacent iterations. This means it's parallelizable.
    result = solve_smt_string(smt_query, "indirect_write_scatter_check")
    assert not result, (
        "Expected indirect write (scatter) to be Not DOFS (parallel) but SMT solver returned SAT."
    )
    print(
        "\nVerdict: PASSED. Indirect Write (Scatter) is Not DOFS (Parallel) as expected."
    )
