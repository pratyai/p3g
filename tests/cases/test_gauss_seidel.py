from pysmt.shortcuts import INT, Int, Minus, Plus, Times, Div

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_gauss_seidel_red_black():
    """
    Test case for Gauss-Seidel with Red-Black ordering (1D).
    This models the two parallel passes of the algorithm.
    Both Red and Black passes are expected to be Not Data-Oblivious Full Sequential (Not DOFS),
    meaning they are parallelizable.

    // Red Pass (odd indices - parallel)
    for i = 1, 3, 5, ...:
        A[i] = A[i-1] + A[i+1]

    // Black Pass (even indices - parallel)
    for i = 2, 4, 6, ...:
        A[i] = A[i-1] + A[i+1]
    """
    print("\n--- Running Test: Gauss-Seidel Red-Black (Expected: Both Passes Not DOFS/Parallel) ---")

    # --- 1. Red Pass Analysis ---
    # Modeled as: for k = 0..N/2-1, i = 2*k+1
    print("\n-- 1. Checking Red Pass for Parallelism (Expected: Not DOFS/Parallel) --")
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

    print(f"Generating SMT query for Red Pass (N symbolic).")
    smt_query_red = generate_smt_for_prove_exists_data_forall_iter_isdep(red_loop_node, loop_end_red_k, verbose=False)
    print("\n--- Generated SMT Query (gauss_seidel_red) ---")
    print(smt_query_red)
    print("-----------------------------------------------")

    # EXPECT: unsat (False) - Red pass is parallel.
    # Writes are to odd indices (2k+1), reads are from even indices (2k, 2k+2).
    # No dependency between iterations for any data configuration.
    result_red = solve_smt_string(smt_query_red, "gauss_seidel_red")
    assert not result_red, "Expected Red Pass to be Not DOFS (parallel) but SMT solver returned SAT."
    print("\nRed Pass Verdict: PASSED. Not fully sequential (DOFS) as expected.")

    # --- 2. Black Pass Analysis ---
    # Modeled as: for k = 0..N/2-2, i = 2*k+2
    print("\n-- 2. Checking Black Pass for Parallelism (Expected: Not DOFS/Parallel) --")
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

    print(f"Generating SMT query for Black Pass (N symbolic).")
    smt_query_black = generate_smt_for_prove_exists_data_forall_iter_isdep(black_loop_node, loop_end_black_k, verbose=False)
    print("\n--- Generated SMT Query (gauss_seidel_black) ---")
    print(smt_query_black)
    print("-------------------------------------------------")

    # EXPECT: unsat (False) - Black pass is parallel.
    # Writes are to even indices (2k+2), reads are from odd indices (2k+1, 2k+3).
    # No dependency between iterations for any data configuration.
    result_black = solve_smt_string(smt_query_black, "gauss_seidel_black")
    assert not result_black, "Expected Black Pass to be Not DOFS (parallel) but SMT solver returned SAT."
    print("\nBlack Pass Verdict: PASSED. Not fully sequential (DOFS) as expected. All checks PASSED.")


def test_gauss_seidel_traditional():
    """
    Test case for the Traditional 1D Gauss-Seidel loop.
    for i = 1 to N-1:
      A[i] = A[i-1] + A[i+1]

    This loop is inherently sequential because A[i] depends on A[i-1],
    which was just computed in the current iteration. This creates a
    Read-After-Write (RAW) dependency between adjacent iterations.
    Therefore, this test expects the loop to be Data-Oblivious Full Sequential (DOFS),
    meaning the SMT query should return SAT.
    """
    print("\n--- Running Test: Traditional Gauss-Seidel (Expected: DOFS/Sequential) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A = b.add_data("A", is_output=True)

    loop_node = None
    with b.add_loop("L1", "k", Int(1), Minus(N, Int(1)),
                    reads=[(A, (Int(0), N))],
                    writes=[(A, (Int(1), Minus(N, Int(1))))]) as L1:
        k = L1.loop_var
        loop_node = L1

        # A[i] = A[i-1] + A[i+1]
        b.add_compute("T1",
                      reads=[(A, Minus(k, Int(1))), (A, Plus(k, Int(1)))],
                      writes=[(A, k)]
                      )

    print_p3g_structure(b.root_graph)

    loop_end = Minus(N, Int(1))
    print(f"Generating SMT query for Traditional Gauss-Seidel (N symbolic).")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end, verbose=False)
    print("\n--- Generated SMT Query (gauss_seidel_traditional) ---")
    print(smt_query)
    print("-----------------------------------------------------")

    # EXPECT: sat (True) - Traditional Gauss-Seidel is sequential due to RAW dependency.
    result = solve_smt_string(smt_query, "gauss_seidel_traditional")
    assert result, "Expected Traditional Gauss-Seidel to be DOFS (sequential) but SMT solver returned UNSAT."
    print("\nVerdict: PASSED. Traditional Gauss-Seidel is DOFS (Sequential) as expected.")
