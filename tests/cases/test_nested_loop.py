from pysmt.shortcuts import Symbol, INT, Int, Minus

from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import build_nested_loop_outer_dofs_graph, build_nested_loop_inner_dofs_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_nested_loop_outer_dofs(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        The outer loop (over 'i') has a true data dependency (A[i,j] depends on A[i-1,j]),
        making it Data-Oblivious Full Sequential (DOFS).
        The inner loop (over 'j') has no self-dependency, making it Not DOFS (parallelizable).
        """
        print(
            "\n--- Running Test: Nested Loop (Expected: Outer DOFS/Sequential, Inner Not DOFS/Parallel) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = build_nested_loop_outer_dofs_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: Not DOFS/Parallel) --"
        )
        # The inner loop has no self-dependencies on 'j'.
        # This means it is Not DOFS (parallelizable).
        smt_query_inner = generate_smt_for_prove_exists_data_forall_iter_isdep(
            L_inner_node, verbose=False
        )
        print("\n--- Generated SMT Query (nested_loop_outer_dofs_inner) ---")
        print(smt_query_inner)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - Inner loop has no self-dependencies on j
        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_outer_dofs_inner_check"
        )
        assert not result_inner, (
            "Expected inner loop to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print("\nInner Loop Verdict: PASSED. Not fully sequential (DOFS) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: DOFS/Sequential) --"
        )
        # The outer loop has a dependency A[i, j] <- A[i-1, j].
        # This means it is Data-Oblivious Full Sequential (DOFS).
        smt_query_outer = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (nested_loop_outer_dofs_outer) ---")
        print(smt_query_outer)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - Outer loop has dependency A[i] <- A[i-1]
        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_outer_dofs_outer_check"
        )
        assert result_outer, (
            "Expected outer loop to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Sequential (DOFS) as expected. All checks PASSED."
        )

    def test_nested_loop_inner_dofs(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        The outer loop (over 'i') has no self-dependency, making it Not DOFS (parallelizable).
        The inner loop (over 'j') has a true data dependency (A[i,j] depends on A[i,j-1]),
        making it Data-Oblivious Full Sequential (DOFS).
        """
        print(
            "\n--- Running Test: Nested Loop (Expected: Outer Not DOFS/Parallel, Inner DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = build_nested_loop_inner_dofs_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: DOFS/Sequential) --"
        )
        # The inner loop has a dependency A[i, j] <- A[i, j-1].
        # This means it is Data-Oblivious Full Sequential (DOFS).
        smt_query_inner = generate_smt_for_prove_exists_data_forall_iter_isdep(
            L_inner_node, verbose=False
        )
        print("\n--- Generated SMT Query (nested_loop_inner_dofs) ---")
        print(smt_query_inner)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - Inner loop has dependency A[j] <- A[j-1]
        result_inner = solve_smt_string(smt_query_inner, "nested_loop_inner_dofs_check")
        assert result_inner, (
            "Expected inner loop to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print("\nInner Loop Verdict: PASSED. Sequential (DOFS) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: Not DOFS/Parallel) --"
        )
        # The outer loop has no self-dependencies on 'i'.
        # This means it is Not DOFS (parallelizable).
        smt_query_outer = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (nested_loop_outer_not_dofs) ---")
        print(smt_query_outer)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - Outer loop has no self-dependencies on i
        result_outer = solve_smt_string(smt_query_outer, "nested_loop_outer_not_dofs_check")
        assert not result_outer, (
            "Expected outer loop to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Not fully sequential (DOFS) as expected. All checks PASSED."
        )


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_nested_loop_outer_dofs_loop_bounds(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS using loop bounds SMT:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]
        """
        print(
            "\n--- Running Test: Nested Loop (Loop Bounds) (Expected: Outer DOFS/Sequential, Inner Not DOFS/Parallel) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = build_nested_loop_outer_dofs_graph()

        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: Not DOFS/Parallel) --"
        )
        smt_query_inner = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            L_inner_node, verbose=False
        )
        print("\n--- Generated SMT Query (nested_loop_outer_dofs_inner_loop_bounds) ---")
        print(smt_query_inner)
        print("-----------------------------------------------")

        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_outer_dofs_inner_loop_bounds_check"
        )
        assert not result_inner, (
            "Expected inner loop (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print("\nInner Loop Verdict: PASSED. Not fully sequential (DOFS) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: DOFS/Sequential) --"
        )
        smt_query_outer = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (nested_loop_outer_dofs_outer_loop_bounds) ---")
        print(smt_query_outer)
        print("-----------------------------------------------")

        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_outer_dofs_outer_loop_bounds_check"
        )
        assert result_outer, (
            "Expected outer loop (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Sequential (DOFS) as expected. All checks PASSED."
        )

    def test_nested_loop_inner_dofs_loop_bounds(self):
        """
        Test case for a Nested Loop with inner loop DOFS using loop bounds SMT:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]
        """
        print(
            "\n--- Running Test: Nested Loop (Loop Bounds) (Expected: Outer Not DOFS/Parallel, Inner DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = build_nested_loop_inner_dofs_graph()

        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: DOFS/Sequential) --"
        )
        smt_query_inner = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            L_inner_node, verbose=False
        )
        print("\n--- Generated SMT Query (nested_loop_inner_dofs_loop_bounds) ---")
        print(smt_query_inner)
        print("-----------------------------------------------")

        result_inner = solve_smt_string(smt_query_inner, "nested_loop_inner_dofs_loop_bounds_check")
        assert result_inner, (
            "Expected inner loop (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print("\nInner Loop Verdict: PASSED. Sequential (DOFS) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: Not DOFS/Parallel) --"
        )
        smt_query_outer = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (nested_loop_outer_not_dofs_loop_bounds) ---")
        print(smt_query_outer)
        print("-----------------------------------------------")

        result_outer = solve_smt_string(smt_query_outer, "nested_loop_outer_not_dofs_loop_bounds_check")
        assert not result_outer, (
            "Expected outer loop (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Not fully sequential (DOFS) as expected. All checks PASSED."
        )
