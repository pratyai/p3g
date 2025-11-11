from pysmt.shortcuts import INT, Int, Minus, GT, LE

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_disprove_dofs
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_long_distance_dependency():
    """
    Loop with long-distance dependency (parallel from DOFS perspective)
    for i = 2...N: A[i] = A[max(i-10, 0)] + B[i]
    """
    print("--- Running Test: Loop with long-distance dependency ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A = b.add_data("A", is_output=True)
    B = b.add_data("B")

    loop_node = None
    with b.add_loop("L1", "k", Int(2), N) as L1:
        k = L1.loop_var
        loop_node = L1

        with b.add_branch("B1") as B1:
            # if k - 10 > 0
            P1 = GT(Minus(k, Int(10)), Int(0))
            with B1.add_path(P1):
                idx = Minus(k, Int(10))
                b.add_compute("T1_gt",
                              reads=[(A, idx), (B, k)],
                              writes=[(A, k)]
                              )
            # else
            P2 = LE(Minus(k, Int(10)), Int(0))
            with B1.add_path(P2):
                idx = Int(0)
                b.add_compute("T2_le",
                              reads=[(A, idx), (B, k)],
                              writes=[(A, k)]
                              )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_disprove_dofs(loop_node, loop_end)

    # EXPECT: sat (True) - No dependency between adjacent iterations.
    result = solve_smt_string(smt_query, "long_distance_dependency")
    assert result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")
