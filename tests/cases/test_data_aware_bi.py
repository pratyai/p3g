from pysmt.shortcuts import Symbol, INT, LE, GT, Int, ArrayType, Select, Minus

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_disprove_dofs
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_data_aware_bi():
    """
    Data-Aware (B[i])
    for i = 1...N: if (B[i] > 0) then A[i] = A[i-1]
    """
    print("--- Running Test: Data-Aware (B[i]) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A = b.add_data("A", is_output=True)
    B_data = b.add_data("B")
    B_val = Symbol("B_val", ArrayType(INT, INT))

    loop_node = None
    with b.add_loop("L1", "k", Int(1), N) as L1:
        k = L1.loop_var
        loop_node = L1

        with b.add_branch("B1") as B1:
            P1 = GT(Select(B_val, k), Int(0))
            with B1.add_path(P1):
                b.add_compute("T1_seq",
                              reads=[(B_data, k), (A, Minus(k, Int(1)))],
                              writes=[(A, k)]
                              )

            P2 = LE(Select(B_val, k), Int(0))
            with B1.add_path(P2):
                b.add_compute("T2_skip",
                              reads=[(B_data, k)],
                              writes=[]
                              )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_disprove_dofs(loop_node, loop_end)

    # EXPECT: unsat (False) - No universal counterexample exists
    result = solve_smt_string(smt_query, "data_aware_bi")
    assert not result
    print("\nVerdict: Sequential (DOFS). All checks PASSED.")
