from pysmt.shortcuts import Int, Minus, Symbol, INT

from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import build_sequential_loop_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_sequential_loop(self):
        """
        Test case for a Sequential Loop: for i = 2...N: A[i] = A[i-1] + B[i].
        This loop has a Read-After-Write (RAW) dependency: A[i] reads A[i-1],
        which was written in the previous iteration. This dependency exists for all
        iterations in the loop range.
        Therefore, the loop is inherently sequential.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT, indicating DOFS (sequential).
        """
        print("\n--- Running Test: Sequential Loop (Expected: DOFS/Sequential) ---")
        b_root_graph, loop_node, N, A_root, B_root = build_sequential_loop_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (sequential_loop) ---")
        print(smt_query)
        print("---------------------------------------------")

        # EXPECT: sat (True) - A data configuration exists that forces sequential execution
        # across all adjacent iterations due to the RAW dependency.
        result = solve_smt_string(smt_query, "sequential_loop_check")
        assert result, (
            "Expected sequential loop to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print("\nVerdict: PASSED. Sequential Loop is DOFS (Sequential) as expected.")


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_sequential_loop_loop_bounds(self):
        """
        Test case for a Sequential Loop using loop bounds SMT: for i = 2...N: A[i] = A[i-1] + B[i].
        This loop has a Read-After-Write (RAW) dependency: A[i] reads A[i-1],
        which was written in the previous iteration. This dependency exists for all
        iterations in the loop range.
        Therefore, the loop is inherently sequential.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT, indicating DOFS (sequential).
        """
        print(
            "\n--- Running Test: Sequential Loop (Loop Bounds) (Expected: DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root = build_sequential_loop_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (sequential_loop_loop_bounds) ---")
        print(smt_query)
        print("---------------------------------------------")

        # EXPECT: sat (True) - A data configuration exists that forces sequential execution
        # across all adjacent iterations due to the RAW dependency.
        result = solve_smt_string(smt_query, "sequential_loop_loop_bounds_check")
        assert result, (
            "Expected sequential loop (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nVerdict: PASSED. Sequential Loop (Loop Bounds) is DOFS (Sequential) as expected."
        )
