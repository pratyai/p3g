from pysmt.shortcuts import INT, Int, Minus

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_disprove_dofs
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_parallel_loop():
    """
    Parallel Loop
    for i in 0:n { a[i] = b[i] + c[i] }
    """
    print("--- Running Test: Parallel Loop ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A = b.add_data("A", is_output=True)
    B = b.add_data("B")
    C = b.add_data("C")

    loop_node = None
    with b.add_loop("L1", "k", Int(0), N) as L1:
        k = L1.loop_var
        loop_node = L1
        b.add_compute("T1",
                      reads=[(B, k), (C, k)],
                      writes=[(A, k)]
                      )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = Minus(N, Int(1))
    smt_query = generate_smt_for_disprove_dofs(loop_node, loop_end)

    # EXPECT: sat (True) - A universal counterexample exists (it's always parallel)
    result = solve_smt_string(smt_query, "parallel_loop")
    assert result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")
