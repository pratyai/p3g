from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import (
    build_gauss_seidel_red_graph,
    build_gauss_seidel_black_graph,
    build_gauss_seidel_traditional_graph,
)
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_gauss_seidel_red_dofs(self):
        """
        Test case for Gauss-Seidel Red Pass (1D).
        Expected to be Not Data-Oblivious Full Sequential (Not DOFS), meaning parallelizable.

        // Red Pass (odd indices - parallel)
        for i = 1, 3, 5, ...:
            A[i] = A[i-1] + A[i+1]
        """
        print("\n--- Running Test: Gauss-Seidel Red Pass (Expected: Not DOFS/Parallel) ---")

        # Modeled as: for k = 0..N/2-1, i = 2*k+1
        print("\n-- Checking Red Pass for Parallelism (Expected: Not DOFS/Parallel) --")
        b_red_root_graph, red_loop_node, N_red, A_red = build_gauss_seidel_red_graph()

        print_p3g_structure(b_red_root_graph)

        print(f"Generating SMT query for Red Pass (N symbolic).")
        smt_query_red = generate_smt_for_prove_exists_data_forall_iter_isdep(
            red_loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (gauss_seidel_red_dofs) ---")
        print(smt_query_red)
        print("-----------------------------------------------")

        # EXPECT: unsat (False) - Red pass is parallel.
        # Writes are to odd indices (2k+1), reads are from even indices (2k, 2k+2).
        # No dependency between iterations for any data configuration.
        result_red = solve_smt_string(smt_query_red, "gauss_seidel_red_dofs")
        assert not result_red, (
            "Expected Red Pass to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print("\nRed Pass Verdict: PASSED. Not fully sequential (DOFS) as expected.")

    def test_gauss_seidel_black_dofs(self):
        """
        Test case for Gauss-Seidel Black Pass (1D).
        Expected to be Not Data-Oblivious Full Sequential (Not DOFS), meaning parallelizable.

        // Black Pass (even indices - parallel)
        for i = 2, 4, 6, ...:
            A[i] = A[i-1] + A[i+1]
        """
        print("\n--- Running Test: Gauss-Seidel Black Pass (Expected: Not DOFS/Parallel) ---")

        # Modeled as: for k = 0..N/2-2, i = 2*k+2
        print("\n-- Checking Black Pass for Parallelism (Expected: Not DOFS/Parallel) --")
        b_black_root_graph, black_loop_node, N_black, A_black = build_gauss_seidel_black_graph()

        print_p3g_structure(b_black_root_graph)

        print(f"Generating SMT query for Black Pass (N symbolic).")
        smt_query_black = generate_smt_for_prove_exists_data_forall_iter_isdep(
            black_loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (gauss_seidel_black_dofs) ---")
        print(smt_query_black)
        print("-------------------------------------------------")

        # EXPECT: unsat (False) - Black pass is parallel.
        # Writes are to even indices (2k+2), reads are from odd indices (2k+1, 2k+3).
        # No dependency between iterations for any data configuration.
        result_black = solve_smt_string(smt_query_black, "gauss_seidel_black_dofs")
        assert not result_black, (
            "Expected Black Pass to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nBlack Pass Verdict: PASSED. Not fully sequential (DOFS) as expected. All checks PASSED."
        )

    def test_gauss_seidel_traditional_dofs(self):
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
        print(
            "\n--- Running Test: Traditional Gauss-Seidel (Expected: DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, N, A = build_gauss_seidel_traditional_graph()

        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for Traditional Gauss-Seidel (N symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (gauss_seidel_traditional_dofs) ---")
        print(smt_query)
        print("-----------------------------------------------------")

        # EXPECT: sat (True) - Traditional Gauss-Seidel is sequential due to RAW dependency.
        result = solve_smt_string(smt_query, "gauss_seidel_traditional_dofs")
        assert result, (
            "Expected Traditional Gauss-Seidel to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nVerdict: PASSED. Traditional Gauss-Seidel is DOFS (Sequential) as expected."
        )


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_gauss_seidel_red_dofs_forall_bounds(self):
        """
        Test case for Gauss-Seidel Red Pass (1D) using loop bounds SMT.
        Expected to be Not Data-Oblivious Full Sequential (Not DOFS), meaning parallelizable.
        """
        print("\n--- Running Test: Gauss-Seidel Red Pass (Loop Bounds) (Expected: Not DOFS/Parallel) ---")

        print("\n-- Checking Red Pass for Parallelism (Expected: Not DOFS/Parallel) --")
        b_red_root_graph, red_loop_node, N_red, A_red = build_gauss_seidel_red_graph()

        print_p3g_structure(b_red_root_graph)

        print(f"Generating SMT query for Red Pass (N symbolic).")
        smt_query_red = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            red_loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (gauss_seidel_red_dofs_forall_bounds) ---")
        print(smt_query_red)
        print("-----------------------------------------------")

        result_red = solve_smt_string(smt_query_red, "gauss_seidel_red_dofs_forall_bounds")
        assert not result_red, (
            "Expected Red Pass (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print("\nRed Pass Verdict: PASSED. Not fully sequential (DOFS) as expected.")

    def test_gauss_seidel_black_dofs_forall_bounds(self):
        """
        Test case for Gauss-Seidel Black Pass (1D) using loop bounds SMT.
        Expected to be Not Data-Oblivious Full Sequential (Not DOFS), meaning parallelizable.
        """
        print("\n--- Running Test: Gauss-Seidel Black Pass (Loop Bounds) (Expected: Not DOFS/Parallel) ---")

        print(
            "\n-- Checking Black Pass for Parallelism (Expected: Not DOFS/Parallel) --"
        )
        b_black_root_graph, black_loop_node, N_black, A_black = build_gauss_seidel_black_graph()

        print_p3g_structure(b_black_root_graph)

        print(f"Generating SMT query for Black Pass (N symbolic).")
        smt_query_black = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            black_loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (gauss_seidel_black_dofs_forall_bounds) ---")
        print(smt_query_black)
        print("-------------------------------------------------")

        result_black = solve_smt_string(smt_query_black, "gauss_seidel_black_dofs_forall_bounds")
        assert not result_black, (
            "Expected Black Pass (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nBlack Pass Verdict: PASSED. Not fully sequential (DOFS) as expected. All checks PASSED."
        )

    def test_gauss_seidel_traditional_dofs_forall_bounds(self):
        """
        Test case for the Traditional 1D Gauss-Seidel loop using loop bounds SMT.
        This loop is inherently sequential because A[i] depends on A[i-1],
        which was just computed in the current iteration.
        """
        print(
            "\n--- Running Test: Traditional Gauss-Seidel (Loop Bounds) (Expected: DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, N, A = build_gauss_seidel_traditional_graph()

        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for Traditional Gauss-Seidel (N symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (gauss_seidel_traditional_dofs_forall_bounds) ---")
        print(smt_query)
        print("-----------------------------------------------------")

        result = solve_smt_string(smt_query, "gauss_seidel_traditional_dofs_forall_bounds")
        assert result, (
            "Expected Traditional Gauss-Seidel (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nVerdict: PASSED. Traditional Gauss-Seidel (Loop Bounds) is DOFS (Sequential) as expected."
        )
