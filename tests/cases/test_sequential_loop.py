from pysmt.shortcuts import INT, Int, Minus

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_disprove_dofs
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_sequential_loop():
    """
    Sequential Loop
    for i = 2...N: A[i] = A[i-1] + B[i]
    """
    print("--- Running Test: Sequential Loop ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A = b.add_data("A", is_output=True)
    B = b.add_data("B")

    loop_node = None
    with b.add_loop("L1", "k", Int(2), N) as L1:
        k = L1.loop_var
        loop_node = L1
        b.add_compute("T1",
                      reads=[(A, Minus(k, Int(1))), (B, k)],
                      writes=[(A, k)]
                      )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_disprove_dofs(loop_node, loop_end)

    # EXPECT: unsat (False) - No universal counterexample exists
    result = solve_smt_string(smt_query, "sequential_loop")
    assert not result
    print("\nVerdict: Sequential (DOFS). All checks PASSED.")
