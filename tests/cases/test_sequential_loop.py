from pysmt.shortcuts import INT, Int, Minus

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_sequential_loop():
    """
    Sequential Loop
    for i = 2...N: A[i] = A[i-1] + B[i]
    """
    print("--- Running Test: Sequential Loop ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")

    loop_node = None
    with b.add_loop("L1", "k", Int(2), N,
                    reads=[(A_root, (Int(1), Minus(N, Int(1)))), (B_root, (Int(2), N))],
                    writes=[(A_root, (Int(2), N))]) as L1:
        k = L1.loop_var
        loop_node = L1
        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        b.add_compute("T1",
                      reads=[(A_local, Minus(k, Int(1))), (B_local, k)],
                      writes=[(A_local, k)]
                      )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end)

    # EXPECT: unsat (False) - No universal counterexample exists
    result = solve_smt_string(smt_query, "sequential_loop")
    assert result
    print("\nVerdict: Sequential (DOFS). All checks PASSED.")
