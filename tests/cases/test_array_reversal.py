from pysmt.shortcuts import Int, GE, Symbol, INT

from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import build_array_reversal_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_array_reversal(self):
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
        b_root_graph, loop_node, N, A_root = build_array_reversal_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic) with no extra assertions.")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (test_array_reversal) ---")
        print(smt_query)
        print("--------------------------------------------------")

        # EXPECT: sat (True) - A data configuration exists that forces sequentiality.
        # For example, if N=2, k=0, j=1, A[0] and A[1] are swapped.
        # If N is symbolic, the solver can pick N=2, which is sequential.
        result = solve_smt_string(smt_query, "array_reversal_dofs_check")
        assert result, (
            "Expected array reversal to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print("\nVerdict: PASSED. Array reversal is DOFS (Sequential) as expected.")

    def test_array_reversal_high_N(self):
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
        print(
            "\n--- Running Test: Array Reversal (Expected: Not DOFS/Parallel for N >= 3) ---"
        )
        b_root_graph, loop_node, N, A_root = build_array_reversal_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic) with extra assertion: N >= 3.")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, extra_assertions=[GE(N, Int(3))], verbose=False
        )
        print("\n--- Generated SMT Query (test_array_reversal_high_N) ---")
        print(smt_query)
        print("---------------------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across all adjacent iterations when N >= 3.
        result = solve_smt_string(smt_query, "array_reversal_not_dofs_check")
        assert not result, (
            "Expected array reversal to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Array reversal is Not DOFS (Parallel) as expected for N >= 3."
        )


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_array_reversal_loop_bounds(self):
        """
        Test case for Array Reversal using generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        The SMT query asserts that the loop runs for at least two iterations.
        If N=2, the loop runs for k=0, j=1, and A[0] and A[1] are swapped, creating a dependency.
        If N is symbolic, the solver can pick N=2, which is sequential.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        print(
            "\n--- Running Test: Array Reversal (Loop Bounds) (Expected: DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, N, A_root = build_array_reversal_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic) with no extra assertions.")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (test_array_reversal_loop_bounds) ---")
        print(smt_query)
        print("-------------------------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across all adjacent iterations when N is universally quantified, because
        # for N >= 3, the loop is parallelizable.
        result = solve_smt_string(smt_query, "array_reversal_loop_bounds_dofs_check")
        assert not result, (
            "Expected array reversal (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Array reversal (Loop Bounds) is Not DOFS (Parallel) as expected."
        )

