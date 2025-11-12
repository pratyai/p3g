from pysmt.shortcuts import Int, GE, Symbol, INT, ArrayType, Select, Minus, LE

from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import build_data_aware_bi_b13_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_data_aware_bi_b13(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        For example, if B[i] = 1 for all i, and B[13] = 0, then B[i] - B[13] > 0 is always true,
        and the loop becomes A[i] = A[i-1], which is sequential.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        print(
            "\n--- Running Test: Data-Aware (B[i] - B[13]) (Expected: DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, B_val, const_idx = build_data_aware_bi_b13_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic) with no extra assertions.")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (data_aware_bi_b13) ---")
        print(smt_query)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - A data configuration exists that forces sequential execution.
        # The SMT solver will find a suitable N and values for B such that the condition
        # (B[i] - B[13] > 0) is always true for all relevant i, making the loop sequential.
        result = solve_smt_string(smt_query, "data_aware_bi_b13_check")
        assert result, (
            "Expected data-aware loop to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print("\nVerdict: PASSED. Data-aware loop is DOFS (Sequential) as expected.")

    def test_data_aware_bi_b13_high_N(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
        This test adds an assertion N >= 15.
        When N >= 15, the loop includes k=13. For k=13, the condition B[13] - B[13] > 0 is false,
        meaning the assignment A[13] = A[12] is skipped.
        Since there's at least one iteration (k=13) where the dependency is not guaranteed,
        the loop is Not Data-Oblivious Full Sequential (Not DOFS), meaning it is parallelizable.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        print(
            "\n--- Running Test: Data-Aware (B[i] - B[13]) High N (Expected: Not DOFS/Parallel) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, B_val, const_idx = build_data_aware_bi_b13_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic) with extra assertion: N >= 15.")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, extra_assertions=[GE(N, Int(15))], verbose=False
        )
        print("\n--- Generated SMT Query (data_aware_bi_b13_high_N) ---")
        print(smt_query)
        print("-----------------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across all adjacent iterations when N >= 15, because the dependency is skipped for k=13.
        result = solve_smt_string(smt_query, "data_aware_bi_b13_high_N_check")
        assert not result, (
            "Expected data-aware loop to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Data-aware loop is Not DOFS (Parallel) as expected for N >= 15."
        )


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_data_aware_bi_b13_loop_bounds(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        For example, if B[i] = 1 for all i, and B[13] = 0, then B[i] - B[13] > 0 is always true,
        and the loop becomes A[i] = A[i-1], which is sequential.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        print(
            "\n--- Running Test: Data-Aware (B[i] - B[13]) (Loop Bounds) (Expected: DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, B_val, const_idx = build_data_aware_bi_b13_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic) with no extra assertions.")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (data_aware_bi_b13_loop_bounds) ---")
        print(smt_query)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across all adjacent iterations when N is universally quantified, because
        # for N >= 15, the loop is parallelizable.
        result = solve_smt_string(smt_query, "data_aware_bi_b13_loop_bounds_check")
        assert not result, (
            "Expected data-aware loop (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Data-aware loop (Loop Bounds) is Not DOFS (Parallel) as expected."
        )
