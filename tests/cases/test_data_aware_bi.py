from pysmt.shortcuts import Symbol, INT, LE, GT, Int, ArrayType, Select, Minus

from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import build_data_aware_bi_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_data_aware_bi(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] > 0) then A[i] = A[i-1].
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        If all B[i] > 0, then A[i] = A[i-1] always executes, creating a sequential dependency.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        print("\n--- Running Test: Data-Aware (B[i]) (Expected: DOFS/Sequential) ---")
        b_root_graph, loop_node, N, A_root, B_root, B_val = build_data_aware_bi_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic) with no extra assertions.")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (data_aware_bi) ---")
        print(smt_query)
        print("-------------------------------------------")

        # EXPECT: sat (True) - A data configuration exists (e.g., all B[i] > 0)
        # that forces sequential execution (A[i] = A[i-1] always executes).
        result = solve_smt_string(smt_query, "data_aware_bi_check")
        assert result, (
            "Expected data-aware loop to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print("\nVerdict: PASSED. Data-aware loop is DOFS (Sequential) as expected.")


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_data_aware_bi_loop_bounds(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] > 0) then A[i] = A[i-1].
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        If all B[i] > 0, then A[i] = A[i-1] always executes, creating a sequential dependency.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        print(
            "\n--- Running Test: Data-Aware (B[i]) (Loop Bounds) (Expected: DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, B_val = build_data_aware_bi_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic) with no extra assertions.")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (data_aware_bi_loop_bounds) ---")
        print(smt_query)
        print("-------------------------------------------")

        # EXPECT: sat (True) - A data configuration exists (e.g., all B[i] > 0)
        # that forces sequential execution (A[i] = A[i-1] always executes).
        result = solve_smt_string(smt_query, "data_aware_bi_loop_bounds_check")
        assert result, (
            "Expected data-aware loop (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nVerdict: PASSED. Data-aware loop (Loop Bounds) is DOFS (Sequential) as expected."
        )
