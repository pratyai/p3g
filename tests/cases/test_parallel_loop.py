from pysmt.shortcuts import INT, Int, Minus

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_parallel_loop():
    """
    Parallel Loop
    for i in 0:n { a[i] = b[i] + c[i] }
    """
    print("--- Running Test: Parallel Loop ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    # Declare the existence of the data containers at the root level
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")
    C_root = b.add_data("C")

    loop_node = None
    with b.add_loop("L1", "k", Int(0), N,
                    reads=[(B_root, (Int(0), N)), (C_root, (Int(0), N))],
                    writes=[(A_root, (Int(0), N))]) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        C_local = b.add_data("C")

        b.add_compute("T1",
                      reads=[(B_local, k), (C_local, k)],
                      writes=[(A_local, k)]
                      )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = Minus(N, Int(1))
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end)

    # EXPECT: sat (True) - A universal counterexample exists (it's always parallel)
    result = solve_smt_string(smt_query, "parallel_loop")
    assert not result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")
