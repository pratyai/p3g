from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.shortcuts import Symbol, INT, ArrayType, Int, Select, GT, Minus, LE

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_disprove_dofs
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_data_aware_bi_b13():
    """
    Data-Aware (B[i] - B[13])
    for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1]
    """
    print("--- Running Test: Data-Aware (B[i] - B[13]) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A = b.add_data("A", is_output=True)
    B_data = b.add_data("B")

    B_val = Symbol("B_val", ArrayType(INT, INT))
    const_idx = Int(13)

    loop_node = None
    with b.add_loop("L1", "k", Int(1), N) as L1:
        k = L1.loop_var
        loop_node = L1

        with b.add_branch("B1") as B1:
            val_k = Select(B_val, k)
            val_13 = Select(B_val, const_idx)

            P1 = GT(Minus(val_k, val_13), Int(0))
            with B1.add_path(P1):
                b.add_compute("T1_seq",
                              reads=[(B_data, k), (B_data, const_idx), (A, Minus(k, Int(1)))],
                              writes=[(A, k)]
                              )

            P2 = LE(Minus(val_k, val_13), Int(0))
            with B1.add_path(P2):
                b.add_compute("T2_skip",
                              reads=[(B_data, k), (B_data, const_idx)],
                              writes=[]
                              )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_disprove_dofs(loop_node, loop_end)

    # EXPECT: sat (True) - Universal counterexample (k=12, N=13) exists
    result = False
    try:
        result = solve_smt_string(smt_query, "data_aware_bi_b13")
    except SolverReturnedUnknownResultError:
        # Conservatively assume sequential for the undecidable case
        print("NOTE: Solver returned 'unknown' for Case 5. Conservatively assuming sequential (False).")
        result = False

    assert result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")
