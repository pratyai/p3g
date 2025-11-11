from pysmt.shortcuts import INT, Int, Minus, GE

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_array_reversal():
    """
    Array Reversal
    for i = 0...N-1: swap(A[i], A[N-1-i])
    """
    print("--- Running Test: Array Reversal ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)

    loop_node = None
    with b.add_loop("L1", "k", Int(0), Minus(N, Int(1)),
                    reads=[(A_root, (Int(0), Minus(N, Int(1))))],
                    writes=[(A_root, (Int(0), Minus(N, Int(1))))]) as L1:
        k = L1.loop_var
        loop_node = L1

        idx_rev = Minus(Minus(N, Int(1)), k)

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)

        b.add_compute("T1_swap",
                      reads=[(A_local, k), (A_local, idx_rev)],
                      writes=[(A_local, k), (A_local, idx_rev)]
                      )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = Minus(N, Int(1))
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end)

    # EXPECT: sat (True) - A universal counterexample (e.g., N=10, k=2) exists
    result = solve_smt_string(smt_query, "array_reversal")
    assert result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")


def test_array_reversal_high_N():
    """
    Array Reversal
    for i = 0...N-1: swap(A[i], A[N-1-i])
    """
    print("--- Running Test: Array Reversal ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)

    loop_node = None
    with b.add_loop("L1", "k", Int(0), Minus(N, Int(1)),
                    reads=[(A_root, (Int(0), Minus(N, Int(1))))],
                    writes=[(A_root, (Int(0), Minus(N, Int(1))))]) as L1:
        k = L1.loop_var
        loop_node = L1

        idx_rev = Minus(Minus(N, Int(1)), k)

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)

        b.add_compute("T1_swap",
                      reads=[(A_local, k), (A_local, idx_rev)],
                      writes=[(A_local, k), (A_local, idx_rev)]
                      )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = Minus(N, Int(1))
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, loop_end, extra_assertions=[GE(N, Int(3))])

    # EXPECT: sat (True) - A universal counterexample (e.g., N=10, k=2) exists
    result = solve_smt_string(smt_query, "array_reversal")
    assert not result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")
