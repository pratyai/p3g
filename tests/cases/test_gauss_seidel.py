from pysmt.shortcuts import INT, Int, Minus, Plus, Times, Div

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_gauss_seidel_red_black():
    """
    Gauss-Seidel with Red-Black ordering (1D)
    This models the two parallel passes of the algorithm.

    // Red Pass (odd indices - parallel)
    for i = 1, 3, 5, ...:
        A[i] = A[i-1] + A[i+1]

    // Black Pass (even indices - parallel)
    for i = 2, 4, 6, ...:
        A[i] = A[i-1] + A[i+1]
    """
    print("--- Running Test: Gauss-Seidel Red-Black ---")

    # --- 1. Red Pass Analysis ---
    # Modeled as: for k = 0..N/2-1, i = 2*k+1
    print("\n-- 1. Checking Red Pass for Parallelism --")
    b_red = GraphBuilder()
    N_red = b_red.add_symbol("N", INT)
    A_red = b_red.add_data("A", is_output=True)

    red_loop_node = None
    # Loop for k from 0 up to (N/2 - 1)
    loop_end_red_k = Minus(Div(N_red, Int(2)), Int(1))
    with b_red.add_loop("L_red", "k", Int(0), loop_end_red_k,
                        reads=[(A_red, (Int(0), Plus(N_red, Int(1))))],
                        writes=[(A_red, (Int(1), N_red))]) as L_red:
        k_red = L_red.loop_var
        red_loop_node = L_red

        # Original index i = 2*k + 1
        i = Plus(Times(Int(2), k_red), Int(1))

        # A[i] = A[i-1] + A[i+1]
        b_red.add_compute("T_red",
                          reads=[(A_red, Minus(i, Int(1))), (A_red, Plus(i, Int(1)))],
                          writes=[(A_red, i)]
                          )

    print_p3g_structure(b_red.root_graph)

    smt_query_red = generate_smt_for_prove_exists_data_forall_iter_isdep(red_loop_node, loop_end_red_k)

    # EXPECT: sat (True) - Red pass is parallel.
    # Writes are to odd indices (2k+1), reads are from even indices (2k, 2k+2).
    # No dependency between iterations.
    result_red = solve_smt_string(smt_query_red, "gauss_seidel_red")
    assert not result_red
    print("\nRed Pass Verdict: Not fully sequential (DOFS).")

    # --- 2. Black Pass Analysis ---
    # Modeled as: for k = 0..N/2-2, i = 2*k+2
    print("\n-- 2. Checking Black Pass for Parallelism --")
    b_black = GraphBuilder()
    N_black = b_black.add_symbol("N", INT)
    A_black = b_black.add_data("A", is_output=True)

    black_loop_node = None
    # Loop for k from 0 up to (N/2 - 2)
    loop_end_black_k = Minus(Div(N_black, Int(2)), Int(2))
    with b_black.add_loop("L_black", "k", Int(0), loop_end_black_k,
                          reads=[(A_black, (Int(1), Plus(N_black, Int(1))))],
                          writes=[(A_black, (Int(2), N_black))]) as L_black:
        k_black = L_black.loop_var
        black_loop_node = L_black

        # Original index i = 2*k + 2
        i = Plus(Times(Int(2), k_black), Int(2))

        # A[i] = A[i-1] + A[i+1]
        b_black.add_compute("T_black",
                          reads=[(A_black, Minus(i, Int(1))), (A_black, Plus(i, Int(1)))],
                          writes=[(A_black, i)]
                          )

    print_p3g_structure(b_black.root_graph)

    smt_query_black = generate_smt_for_prove_exists_data_forall_iter_isdep(black_loop_node, loop_end_black_k)

    # EXPECT: sat (True) - Black pass is parallel.
    # Writes are to even indices (2k+2), reads are from odd indices (2k+1, 2k+3).
    # No dependency between iterations.
    result_black = solve_smt_string(smt_query_black, "gauss_seidel_black")
    assert not result_black
    print("\nBlack Pass Verdict: Not fully sequential (DOFS). All checks PASSED.")
