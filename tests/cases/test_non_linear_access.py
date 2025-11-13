from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import build_non_linear_access_graph, build_non_linear_access_sequential_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_non_linear_access_dofs(self):
        """
        Test case for a loop with a Non-linear Array Access:
        for i=0:N: A[i*i] = B[i] + C[i]
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        The non-linear access pattern `i*i` ensures that for `i > 0`, `i*i` and `(i+1)*(i+1)`
        are distinct and sufficiently far apart to avoid adjacent iteration dependencies.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        print("\n--- Running Test: Non-linear Array Access (Expected: Not DOFS/Parallel) ---")
        b_root_graph, loop_node, N, A_root, B_root, C_root = build_non_linear_access_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (non_linear_access_dofs) ---")
        print(smt_query)
        print("--------------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across all adjacent iterations, as the non-linear access makes it parallel.
        result = solve_smt_string(smt_query, "non_linear_access_dofs")
        assert not result, (
            "Expected non-linear array access loop to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Non-linear Array Access loop is Not DOFS (Parallel) as expected."
        )

    def test_non_linear_access_sequential_dofs(self):
        """
        Test case for a loop with a Non-linear Array Access that is sequential:
        for i = 1...N: A[i*i] = A[(i-1)*(i-1)] + B[i]
        This loop has a Read-After-Write (RAW) dependency: A[i*i] reads A[(i-1)*(i-1)],
        which was written in the previous iteration. This dependency exists for all
        iterations in the loop range.
        Therefore, the loop is inherently sequential.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT, indicating DOFS (sequential).
        """
        print("\n--- Running Test: Non-linear Array Access Sequential (Expected: DOFS/Sequential) ---")
        b_root_graph, loop_node, N, A_root, B_root = build_non_linear_access_sequential_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (non_linear_access_sequential_dofs) ---")
        print(smt_query)
        print("-------------------------------------------------------------")

        # EXPECT: sat (True) - A data configuration exists that forces sequential execution
        # across all adjacent iterations due to the RAW dependency.
        result = solve_smt_string(smt_query, "non_linear_access_sequential_dofs")
        assert result, (
            "Expected non-linear array access sequential loop to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print("\nVerdict: PASSED. Non-linear Array Access Sequential loop is DOFS (Sequential) as expected.")


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_non_linear_access_dofs_forall_bounds(self):
        """
        Test case for a loop with a Non-linear Array Access using loop bounds SMT:
        for i=0:N: A[i*i] = B[i] + C[i]
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        The non-linear access pattern `i*i` ensures that for `i > 0`, `i*i` and `(i+1)*(i+1)`
        are distinct and sufficiently far apart to avoid adjacent iteration dependencies.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        print(
            "\n--- Running Test: Non-linear Array Access (Loop Bounds) (Expected: Not DOFS/Parallel) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, C_root = build_non_linear_access_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (non_linear_access_dofs_forall_bounds) ---")
        print(smt_query)
        print("--------------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across all adjacent iterations, as the non-linear access makes it parallel.
        result = solve_smt_string(smt_query, "non_linear_access_dofs_forall_bounds")
        assert not result, (
            "Expected non-linear array access loop (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Non-linear Array Access loop (Loop Bounds) is Not DOFS (Parallel) as expected."
        )

    def test_non_linear_access_sequential_dofs_forall_bounds(self):
        """
        Test case for a loop with a Non-linear Array Access that is sequential using loop bounds SMT:
        for i = 1...N: A[i*i] = A[(i-1)*(i-1)] + B[i]
        This loop has a Read-After-Write (RAW) dependency: A[i*i] reads A[(i-1)*(i-1)],
        which was written in the previous iteration. This dependency exists for all
        iterations in the loop range.
        Therefore, the loop is inherently sequential.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT, indicating DOFS (sequential).
        """
        print(
            "\n--- Running Test: Non-linear Array Access Sequential (Loop Bounds) (Expected: DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root = build_non_linear_access_sequential_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (non_linear_access_sequential_dofs_forall_bounds) ---")
        print(smt_query)
        print("-------------------------------------------------------------")

        # EXPECT: sat (True) - A data configuration exists that forces sequential execution
        # across all adjacent iterations due to the RAW dependency.
        result = solve_smt_string(smt_query, "non_linear_access_sequential_dofs_forall_bounds")
        assert result, (
            "Expected non-linear array access sequential loop (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nVerdict: PASSED. Non-linear Array Access Sequential loop (Loop Bounds) is DOFS (Sequential) as expected."
        )
