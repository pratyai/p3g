from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_forall_iter_isindep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
)
from tests.cases.graph_definitions import (
    build_nested_loop_outer_dofs_graph,
    build_nested_loop_inner_dofs_graph,
)
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
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_outer_dofs_graph()
        )

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
            smt_query_inner, "nested_loop_outer_dofs_inner_dofs"
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
        print("\n--- Generated SMT Query (nested_loop_outer_dofs_outer_dofs) ---")
        print(smt_query_outer)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - Outer loop has dependency A[i] <- A[i-1]
        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_outer_dofs_outer_dofs"
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
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_inner_dofs_graph()
        )

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
        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_inner_dofs_inner_dofs"
        )
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
        print("\n--- Generated SMT Query (nested_loop_inner_dofs_outer_dofs) ---")
        print(smt_query_outer)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - Outer loop has no self-dependencies on i
        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_inner_dofs_outer_dofs"
        )
        assert not result_outer, (
            "Expected outer loop to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Not fully sequential (DOFS) as expected. All checks PASSED."
        )


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_nested_loop_outer_dofs_forall_bounds(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS using loop bounds SMT:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]
        """
        print(
            "\n--- Running Test: Nested Loop (Loop Bounds) (Expected: Outer DOFS/Sequential, Inner Not DOFS/Parallel) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_outer_dofs_graph()
        )

        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: Not DOFS/Parallel) --"
        )
        smt_query_inner = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
                L_inner_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_outer_dofs_inner_dofs_forall_bounds) ---"
        )
        print(smt_query_inner)
        print("-----------------------------------------------")

        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_outer_dofs_inner_dofs_forall_bounds"
        )
        assert not result_inner, (
            "Expected inner loop (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print("\nInner Loop Verdict: PASSED. Not fully sequential (DOFS) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: DOFS/Sequential) --"
        )
        smt_query_outer = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
                loop_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_outer_dofs_outer_dofs_forall_bounds) ---"
        )
        print(smt_query_outer)
        print("-----------------------------------------------")

        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_outer_dofs_outer_dofs_forall_bounds"
        )
        assert result_outer, (
            "Expected outer loop (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Sequential (DOFS) as expected. All checks PASSED."
        )

    def test_nested_loop_inner_dofs_forall_bounds(self):
        """
        Test case for a Nested Loop with inner loop DOFS using loop bounds SMT:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]
        """
        print(
            "\n--- Running Test: Nested Loop (Loop Bounds) (Expected: Outer Not DOFS/Parallel, Inner DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_inner_dofs_graph()
        )

        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: DOFS/Sequential) --"
        )
        smt_query_inner = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
                L_inner_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_inner_dofs_inner_dofs_forall_bounds) ---"
        )
        print(smt_query_inner)
        print("-----------------------------------------------")

        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_inner_dofs_inner_dofs_forall_bounds"
        )
        assert result_inner, (
            "Expected inner loop (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print("\nInner Loop Verdict: PASSED. Sequential (DOFS) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: Not DOFS/Parallel) --"
        )
        smt_query_outer = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
                loop_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_inner_dofs_outer_dofs_forall_bounds) ---"
        )
        print(smt_query_outer)
        print("-----------------------------------------------")

        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_inner_dofs_outer_dofs_forall_bounds"
        )
        assert not result_outer, (
            "Expected outer loop (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Not fully sequential (DOFS) as expected. All checks PASSED."
        )


class TestProveExistsDataForallIterIsindep:
    def test_nested_loop_outer_dofs_dofi(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        The outer loop is sequential, so it should be NOT DOFI.
        The inner loop is parallel, so it should be DOFI.
        """
        print(
            "--- Running Test: Nested Loop DOFI (Expected: Outer Not DOFI/Sequential, Inner DOFI/Parallel) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_outer_dofs_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: DOFI/Parallel) --"
        )
        smt_query_inner = generate_smt_for_prove_exists_data_forall_iter_isindep(
            L_inner_node, verbose=False
        )
        print("--- Generated SMT Query (nested_loop_outer_dofs_inner_dofi) ---")
        print(smt_query_inner)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - Inner loop is parallel.
        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_outer_dofs_inner_dofi"
        )
        assert result_inner, (
            "Expected inner loop to be DOFI (parallel) but SMT solver returned UNSAT."
        )
        print("Inner Loop Verdict: PASSED. DOFI (Parallel) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: Not DOFI/Sequential) --"
        )
        smt_query_outer = generate_smt_for_prove_exists_data_forall_iter_isindep(
            loop_node, verbose=False
        )
        print("--- Generated SMT Query (nested_loop_outer_dofs_outer_dofi) ---")
        print(smt_query_outer)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - Outer loop is sequential.
        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_outer_dofs_outer_dofi"
        )
        assert not result_outer, (
            "Expected outer loop to be Not DOFI (sequential) but SMT solver returned SAT."
        )
        print(
            "Outer Loop Verdict: PASSED. Not DOFI (Sequential) as expected. All checks PASSED."
        )

    def test_nested_loop_inner_dofs_dofi(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        The outer loop is parallel, so it should be DOFI.
        The inner loop is sequential, so it should be NOT DOFI.
        """
        print(
            "--- Running Test: Nested Loop DOFI (Expected: Outer DOFI/Parallel, Inner Not DOFI/Sequential) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_inner_dofs_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: Not DOFI/Sequential) --"
        )
        smt_query_inner = generate_smt_for_prove_exists_data_forall_iter_isindep(
            L_inner_node, verbose=False
        )
        print("--- Generated SMT Query (nested_loop_inner_dofs_inner_dofi) ---")
        print(smt_query_inner)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - Inner loop is sequential.
        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_inner_dofs_inner_dofi"
        )
        assert not result_inner, (
            "Expected inner loop to be Not DOFI (sequential) but SMT solver returned SAT."
        )
        print("Inner Loop Verdict: PASSED. Not DOFI (Sequential) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: DOFI/Parallel) --"
        )
        smt_query_outer = generate_smt_for_prove_exists_data_forall_iter_isindep(
            loop_node, verbose=False
        )
        print("--- Generated SMT Query (nested_loop_inner_dofs_outer_dofi) ---")
        print(smt_query_outer)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - Outer loop is parallel.
        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_inner_dofs_outer_dofi"
        )
        assert result_outer, (
            "Expected outer loop to be DOFI (parallel) but SMT solver returned UNSAT."
        )
        print(
            "Outer Loop Verdict: PASSED. DOFI (Parallel) as expected. All checks PASSED."
        )


class TestProveExistsDataForallLoopBoundsIterIsindep:
    def test_nested_loop_outer_dofs_dofi_forall_bounds(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        The outer loop is sequential, so it should be NOT DOFI.
        The inner loop is parallel, so it should be DOFI.
        This test uses universally quantified loop bounds.
        """
        print(
            "\n--- Running Test: Nested Loop DOFI (Loop Bounds) (Expected: Outer Not DOFI/Sequential, Inner DOFI/Parallel) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_outer_dofs_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: DOFI/Parallel) --"
        )
        smt_query_inner = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep(
                L_inner_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_outer_dofs_inner_dofi_forall_bounds) ---"
        )
        print(smt_query_inner)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - Inner loop is parallel.
        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_outer_dofs_inner_dofi_forall_bounds"
        )
        assert result_inner, (
            "Expected inner loop (loop bounds) to be DOFI (parallel) but SMT solver returned UNSAT."
        )
        print("\nInner Loop Verdict: PASSED. DOFI (Parallel) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: Not DOFI/Sequential) --"
        )
        smt_query_outer = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep(
                loop_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_outer_dofs_outer_dofi_forall_bounds) ---"
        )
        print(smt_query_outer)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - Outer loop is sequential.
        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_outer_dofs_outer_dofi_forall_bounds"
        )
        assert not result_outer, (
            "Expected outer loop (loop bounds) to be Not DOFI (sequential) but SMT solver returned SAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Not DOFI (Sequential) as expected. All checks PASSED."
        )

    def test_nested_loop_inner_dofs_dofi_forall_bounds(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        The outer loop is parallel, so it should be DOFI.
        The inner loop is sequential, so it should be NOT DOFI.
        This test uses universally quantified loop bounds.
        """
        print(
            "\n--- Running Test: Nested Loop DOFI (Loop Bounds) (Expected: Outer DOFI/Parallel, Inner Not DOFI/Sequential) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_inner_dofs_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: Not DOFI/Sequential) --"
        )
        smt_query_inner = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep(
                L_inner_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_inner_dofs_inner_dofi_forall_bounds) ---"
        )
        print(smt_query_inner)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - Inner loop is sequential.
        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_inner_dofs_inner_dofi_forall_bounds"
        )
        assert not result_inner, (
            "Expected inner loop (loop bounds) to be Not DOFI (sequential) but SMT solver returned SAT."
        )
        print("\nInner Loop Verdict: PASSED. Not DOFI (Sequential) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: DOFI/Parallel) --"
        )
        smt_query_outer = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep(
                loop_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_inner_dofs_outer_dofi_forall_bounds) ---"
        )
        print(smt_query_outer)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - Outer loop is parallel.
        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_inner_dofs_outer_dofi_forall_bounds"
        )
        assert result_outer, (
            "Expected outer loop (loop bounds) to be DOFI (parallel) but SMT solver returned UNSAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. DOFI (Parallel) as expected. All checks PASSED."
        )


class TestProveForallDataForallLoopBoundsIterIsindep:
    def test_nested_loop_outer_dofs_forall_data_forall_bounds(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        The outer loop is sequential, so it should be NOT DOFI.
        The inner loop is parallel, so it should be DOFI.
        This test uses universally quantified data and loop bounds.
        """
        print(
            "\n--- Running Test: Nested Loop (Forall Data, Forall Loop Bounds) (Expected: Outer Not DOFI/Sequential, Inner DOFI/Parallel) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_outer_dofs_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: DOFI/Parallel) --"
        )
        smt_query_inner = (
            generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep(
                L_inner_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_outer_dofs_inner_forall_data_forall_bounds) ---"
        )
        print(smt_query_inner)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - Inner loop is parallel.
        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_outer_dofs_inner_forall_data_forall_bounds"
        )
        assert result_inner, (
            "Expected inner loop (forall data, forall loop bounds) to be DOFI (parallel) but SMT solver returned UNSAT."
        )
        print("\nInner Loop Verdict: PASSED. DOFI (Parallel) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: Not DOFI/Sequential) --"
        )
        smt_query_outer = (
            generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep(
                loop_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_outer_dofs_outer_forall_data_forall_bounds) ---"
        )
        print(smt_query_outer)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - Outer loop is sequential.
        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_outer_dofs_outer_forall_data_forall_bounds"
        )
        assert not result_outer, (
            "Expected outer loop (forall data, forall loop bounds) to be Not DOFI (sequential) but SMT solver returned SAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. Not DOFI (Sequential) as expected. All checks PASSED."
        )

    def test_nested_loop_inner_dofs_forall_data_forall_bounds(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        The outer loop is parallel, so it should be DOFI.
        The inner loop is sequential, so it should be NOT DOFI.
        This test uses universally quantified data and loop bounds.
        """
        print(
            "\n--- Running Test: Nested Loop (Forall Data, Forall Loop Bounds) (Expected: Outer DOFI/Parallel, Inner Not DOFI/Sequential) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_inner_dofs_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        # --- 1. Check Inner Loop (L_inner) ---
        print(
            "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: Not DOFI/Sequential) --"
        )
        smt_query_inner = (
            generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep(
                L_inner_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_inner_dofs_inner_forall_data_forall_bounds) ---"
        )
        print(smt_query_inner)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - Inner loop is sequential.
        result_inner = solve_smt_string(
            smt_query_inner, "nested_loop_inner_dofs_inner_forall_data_forall_bounds"
        )
        assert not result_inner, (
            "Expected inner loop (forall data, forall loop bounds) to be Not DOFI (sequential) but SMT solver returned SAT."
        )
        print("\nInner Loop Verdict: PASSED. Not DOFI (Sequential) as expected.")

        # --- 2. Check Outer Loop (L_outer) ---
        print(
            "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: DOFI/Parallel) --"
        )
        smt_query_outer = (
            generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep(
                loop_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_inner_dofs_outer_forall_data_forall_bounds) ---"
        )
        print(smt_query_outer)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - Outer loop is parallel.
        result_outer = solve_smt_string(
            smt_query_outer, "nested_loop_inner_dofs_outer_forall_data_forall_bounds"
        )
        assert result_outer, (
            "Expected outer loop (forall data, forall loop bounds) to be DOFI (parallel) but SMT solver returned UNSAT."
        )
        print(
            "\nOuter Loop Verdict: PASSED. DOFI (Parallel) as expected. All checks PASSED."
        )


class TestProveExistsDataExistsLoopBoundsExistsIterIsdep:
    def test_nested_loop_outer_dofs_find_dependency(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        This test uses the relaxed SMT query to find *any* dependency.
        The outer loop has a RAW dependency, so a dependency should be found.
        The SMT query should return SAT.
        """
        print(
            "\n--- Running Test: Nested Loop (Outer DOFS) (Find Dependency) (Expected: SAT) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_outer_dofs_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N, M (symbolic).")
        smt_query = (
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep(
                loop_node, verbose=False
            )
        )
        print("\n--- Generated SMT Query (nested_loop_outer_dofs_find_dependency) ---")
        print(smt_query)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - A dependency should be found.
        result = solve_smt_string(smt_query, "nested_loop_outer_dofs_find_dependency")
        assert result, (
            "Expected to find a dependency for nested outer DOFS loop but SMT solver returned UNSAT."
        )
        print(
            "\nVerdict: PASSED. Found a dependency for Nested Outer DOFS Loop as expected."
        )

    def test_nested_loop_outer_dofs_inner_find_dependency(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        This test uses the relaxed SMT query to find *any* dependency.
        The inner loop is fully parallel, so no dependency should be found.
        The SMT query should return UNSAT.
        """
        print(
            "\n--- Running Test: Nested Loop (Outer DOFS, Inner) (Find Dependency) (Expected: UNSAT) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_outer_dofs_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N, M (symbolic).")
        smt_query = (
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep(
                L_inner_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_outer_dofs_inner_find_dependency) ---"
        )
        print(smt_query)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - No dependency should be found.
        result = solve_smt_string(
            smt_query, "nested_loop_outer_dofs_inner_find_dependency"
        )
        assert not result, (
            "Expected to find no dependency for nested outer DOFS inner loop but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Found no dependency for Nested Outer DOFS Inner Loop as expected."
        )

    def test_nested_loop_inner_dofs_find_dependency(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        This test uses the relaxed SMT query to find *any* dependency.
        The outer loop is fully parallel, so no dependency should be found.
        The SMT query should return UNSAT.
        """
        print(
            "\n--- Running Test: Nested Loop (Inner DOFS) (Find Dependency) (Expected: UNSAT) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_inner_dofs_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N, M (symbolic).")
        smt_query = (
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep(
                loop_node, verbose=False
            )
        )
        print("\n--- Generated SMT Query (nested_loop_inner_dofs_find_dependency) ---")
        print(smt_query)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - No dependency should be found.
        result = solve_smt_string(smt_query, "nested_loop_inner_dofs_find_dependency")
        assert not result, (
            "Expected to find no dependency for nested inner DOFS loop but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Found no dependency for Nested Inner DOFS Loop as expected."
        )

    def test_nested_loop_inner_dofs_inner_find_dependency(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        This test uses the relaxed SMT query to find *any* dependency.
        The inner loop has a RAW dependency, so a dependency should be found.
        The SMT query should return SAT.
        """
        print(
            "\n--- Running Test: Nested Loop (Inner DOFS, Inner) (Find Dependency) (Expected: SAT) ---"
        )
        b_root_graph, loop_node, L_inner_node, N, M, A_root, B_root = (
            build_nested_loop_inner_dofs_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N, M (symbolic).")
        smt_query = (
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep(
                L_inner_node, verbose=False
            )
        )
        print(
            "\n--- Generated SMT Query (nested_loop_inner_dofs_inner_find_dependency) ---"
        )
        print(smt_query)
        print("-----------------------------------------------")

        # EXPECT: sat (True) - A dependency should be found.
        result = solve_smt_string(
            smt_query, "nested_loop_inner_dofs_inner_find_dependency"
        )
        assert result, (
            "Expected to find a dependency for nested inner DOFS inner loop but SMT solver returned UNSAT."
        )
        print(
            "\nVerdict: PASSED. Found a dependency for Nested Inner DOFS Inner Loop as expected."
        )
