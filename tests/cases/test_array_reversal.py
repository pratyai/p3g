from pysmt.shortcuts import INT, Int, Minus, GE

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_array_reversal():
    """
    Test case for Array Reversal: for i = 0...N-1: swap(A[i], A[N-1-i]).
    This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
    meaning there exists a data configuration that forces sequential execution.
    The SMT query asserts that the loop runs for at least two iterations.
    If N=2, the loop runs for k=0, j=1, and A[0] and A[1] are swapped, creating a dependency.
    If N is symbolic, the solver can pick N=2, which is sequential.
    The SMT query should return SAT, indicating DOFS (sequential).
    """
    print("\n--- Running Test: Array Reversal (Expected: DOFS/Sequential) ---")
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
    print(f"Generating SMT query for N (symbolic) with no extra assertions.")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end, verbose=False)
    print("\n--- Generated SMT Query (test_array_reversal) ---")
    print(smt_query)
    print("--------------------------------------------------")

    # EXPECT: sat (True) - A data configuration exists that forces sequentiality.
    # For example, if N=2, k=0, j=1, A[0] and A[1] are swapped.
    # If N is symbolic, the solver can pick N=2, which is sequential.
    result = solve_smt_string(smt_query, "array_reversal_dofs_check")
    assert result, "Expected array reversal to be DOFS (sequential) but SMT solver returned UNSAT."
    print("\nVerdict: PASSED. Array reversal is DOFS (Sequential) as expected.")


def test_array_reversal_high_N():
    """
    Test case for Array Reversal with N >= 3.
    This test expects the loop to be NOT Data-Oblivious Full Sequential (DOFS),
    meaning it is parallelizable.
    When N >= 3, for any k, the indices k and N-1-k are distinct and
    do not overlap with (k+1) and N-1-(k+1) for all valid k.
    This means there is no data configuration that forces sequential execution
    across all adjacent iterations.
    The SMT query should return UNSAT, indicating Not DOFS (parallel).
    """
    print("\n--- Running Test: Array Reversal (Expected: Not DOFS/Parallel for N >= 3) ---")
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
    print(f"Generating SMT query for N (symbolic) with extra assertion: N >= 3.")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, loop_end, extra_assertions=[GE(N, Int(3))], verbose=False)
    print("\n--- Generated SMT Query (test_array_reversal_high_N) ---")
    print(smt_query)
    print("---------------------------------------------------------")

    # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
    # across all adjacent iterations when N >= 3.
    result = solve_smt_string(smt_query, "array_reversal_not_dofs_check")
    assert not result, "Expected array reversal to be Not DOFS (parallel) but SMT solver returned SAT."
    print("\nVerdict: PASSED. Array reversal is Not DOFS (Parallel) as expected for N >= 3.")
