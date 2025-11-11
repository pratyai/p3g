from pysmt.shortcuts import INT, Int, Minus, GT, LE, Symbol

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_disprove_dofs
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_sequential_with_symbolic_max_index():
    """
    Sequential Loop with max(i-w, 0) index, where w is a symbol.
    for i = 2...N: A[i] = A[max(i-w, 0)] + B[i]
    """
    print("--- Running Test: Sequential Loop with symbolic max(i-w, 0) index ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    w = b.add_symbol("w", INT)
    A = b.add_data("A", is_output=True)
    B = b.add_data("B")

    loop_node = None
    with b.add_loop("L1", "k", Int(2), N) as L1:
        k = L1.loop_var
        loop_node = L1

        with b.add_branch("B1") as B1:
            # if k - w > 0
            P1 = GT(Minus(k, w), Int(0))
            with B1.add_path(P1):
                idx = Minus(k, w)
                b.add_compute("T1_gt",
                              reads=[(A, idx), (B, k)],
                              writes=[(A, k)]
                              )
            # else
            P2 = LE(Minus(k, w), Int(0))
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

    # EXPECT: unsat (False) - A dependency can exist (e.g., w=1), so no universal counterexample.
    result = solve_smt_string(smt_query, "sequential_with_symbolic_max_index")
    assert not result
    print("\nVerdict: Sequential (DOFS). All checks PASSED.")
