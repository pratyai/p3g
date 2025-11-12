from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import build_cholesky_full_kernel_graph, build_cholesky_sequential_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_cholesky_sequential_dofs(self):
        """
        Cholesky Decomposition-like kernel (fully sequential)
        for i = 2...N:
          for j = 2...i:
            L[i, j] = L[i, j-1] + L[j-1, j-1]

        # Actual Cholesky inner kernel (simplified for L[i,j] calculation):
        # L[i,j] = (A[i,j] - sum_{k=0}^{j-1} L[i,k] * L[j,k]) / L[j,j]
        # This test models a simplified dependency pattern found in such kernels.
        """
        print("\n--- Running Test: Cholesky Decomposition-like Kernel (Simplified) ---")
        print("Expected: Inner Loop DOFS (Sequential), Outer Loop Not DOFS (Parallel)")
        b_root_graph, outer_loop_node, inner_loop_node, N, L_root = build_cholesky_sequential_graph()

        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: DOFS/Sequential) --"
        )
        # The inner loop has a dependency L[i,j] <- L[i,j-1].
        # This means it is fully sequential (DOFS).
        # The inner loop end 'i' is a symbolic variable for this check.
        smt_query_inner = generate_smt_for_prove_exists_data_forall_iter_isdep(
            inner_loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (cholesky_sequential_inner_dofs) ---")
        print(smt_query_inner)
        print("--------------------------------------------")

        # EXPECT: sat (True) - Inner loop has dependency L[i,j] <- L[i,j-1]
        result_inner = solve_smt_string(smt_query_inner, "cholesky_sequential_inner_dofs")
        assert result_inner, (
            "Expected inner loop to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print("\nInner Loop Verdict: PASSED. Sequential (DOFS) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: Not DOFS/Parallel) --"
        )
        # The outer loop has a dependency through L[j-1,j-1] (e.g., when j=i, L[i,i] depends on L[i-1,i-1]).
        # However, this dependency is not *always* present for *all* adjacent iterations (k, k+1)
        # for a *single* data configuration.
        # For example, if N is large enough, and we pick a data configuration where L[j-1,j-1]
        # is always distinct for different j, then the outer loop might appear parallel.
        # The current model implies that for N >= 3, the outer loop is parallelizable.
        smt_query_outer = generate_smt_for_prove_exists_data_forall_iter_isdep(
            outer_loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (cholesky_sequential_outer_dofs) ---")
        print(smt_query_outer)
        print("--------------------------------------------")

        # EXPECT: unsat (False) - Outer loop is Not DOFS (Parallel)
        result_outer = solve_smt_string(smt_query_outer, "cholesky_sequential_outer_dofs")
        assert not result_outer, (
            "Expected outer loop to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Not DOFS (Parallel) as expected. All checks PASSED."
        )

    def test_cholesky_full_kernel_dofs(self):
        """
        More accurate Cholesky Decomposition kernel (fully sequential)
        for i = 0 to N-1:
          for j = 0 to i:
            sum_val = 0
            for k = 0 to j-1:
              sum_val = sum_val + L[i,k] * L[j,k]
            // L[i,j] = (A[i,j] - sum_val) / L[j,j]
            // (Simplified to L[i,j] = A[i,j] - sum_val for P3G modeling)

        This test expects the full Cholesky kernel to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        """
        print("\n--- Running Test: Full Cholesky Kernel (Expected: DOFS/Sequential) ---")
        (
            b_root_graph,
            outer_loop_node,
            middle_loop_node,
            inner_loop_node,
            N,
            A_root,
            L_root,
            A_val,
            L_val,
        ) = build_cholesky_full_kernel_graph()

        print_p3g_structure(b_root_graph)

        # --- Check Outer Loop (L_outer) ---
        print(
            "\n-- Checking Full Cholesky Kernel (L_outer) for Parallelism (Expected: DOFS/Sequential) --"
        )
        # The full Cholesky kernel is known to be highly sequential due to dependencies
        # across all three nested loops.
        smt_query_outer = generate_smt_for_prove_exists_data_forall_iter_isdep(
            outer_loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (cholesky_full_kernel_dofs) ---")
        print(smt_query_outer)
        print("---------------------------------------------------")

        # EXPECT: sat (True) - Full Cholesky is highly sequential
        result_outer = solve_smt_string(smt_query_outer, "cholesky_full_kernel_dofs")
        assert result_outer, (
            "Expected full Cholesky kernel to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nFull Cholesky Kernel Verdict: PASSED. Sequential (DOFS) as expected. All checks PASSED."
        )


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_cholesky_sequential_dofs_forall_bounds(self):
        """
        Cholesky Decomposition-like kernel (fully sequential)
        for i = 2...N:
          for j = 2...i:
            L[i, j] = L[i, j-1] + L[j-1, j-1]

        This test expects the inner loop to be DOFS (Sequential) and the outer loop to be Not DOFS (Parallel)
        when using generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep.
        """
        print(
            "\n--- Running Test: Cholesky Decomposition-like Kernel (Loop Bounds) (Simplified) ---"
        )
        print("Expected: Inner Loop DOFS (Sequential), Outer Loop Not DOFS (Parallel)")
        b_root_graph, outer_loop_node, inner_loop_node, N, L_root = build_cholesky_sequential_graph()

        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: DOFS/Sequential) --"
        )
        smt_query_inner = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            inner_loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (cholesky_sequential_inner_dofs_forall_bounds) ---")
        print(smt_query_inner)
        print("--------------------------------------------")

        result_inner = solve_smt_string(smt_query_inner, "cholesky_sequential_inner_dofs_forall_bounds")
        assert result_inner, (
            "Expected inner loop (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print("\nInner Loop Verdict: PASSED. Sequential (DOFS) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: Not DOFS/Parallel) --"
        )
        smt_query_outer = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            outer_loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (cholesky_sequential_outer_dofs_forall_bounds) ---")
        print(smt_query_outer)
        print("--------------------------------------------")

        result_outer = solve_smt_string(smt_query_outer, "cholesky_sequential_outer_dofs_forall_bounds")
        assert not result_outer, (
            "Expected outer loop (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Not DOFS (Parallel) as expected. All checks PASSED."
        )

    def test_cholesky_full_kernel_dofs_forall_bounds(self):
        """
        More accurate Cholesky Decomposition kernel (fully sequential)
        This test expects the full Cholesky kernel to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        """
        print("\n--- Running Test: Full Cholesky Kernel (Loop Bounds) (Expected: DOFS/Sequential) ---")
        (
            b_root_graph,
            outer_loop_node,
            middle_loop_node,
            inner_loop_node,
            N,
            A_root,
            L_root,
            A_val,
            L_val,
        ) = build_cholesky_full_kernel_graph()

        print_p3g_structure(b_root_graph)

        # --- Check Outer Loop (L_outer) ---
        print(
            "\n-- Checking Full Cholesky Kernel (L_outer) for Parallelism (Expected: DOFS/Sequential) --"
        )
        smt_query_outer = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            outer_loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (cholesky_full_kernel_dofs_forall_bounds) ---")
        print(smt_query_outer)
        print("---------------------------------------------------")

        result_outer = solve_smt_string(smt_query_outer, "cholesky_full_kernel_dofs_forall_bounds")
        assert result_outer, (
            "Expected full Cholesky kernel (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nFull Cholesky Kernel Verdict: PASSED. Sequential (DOFS) as expected. All checks PASSED."
        )
