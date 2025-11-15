from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import build_sequential_with_symbolic_max_index_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_sequential_with_symbolic_max_index_dofs(self):
        """
        Test case for a Sequential Loop with max(i-w, 0) index, where w is a symbolic variable.
        for i = 2...N: A[i] = A[max(i-w, 0)] + B[i]
        Since 'w' is a symbolic variable, the SMT solver can choose a value for 'w' (e.g., w=1)
        that makes the loop sequential (A[i] = A[max(i-1, 0)] + B[i] becomes A[i] = A[i-1] + B[i] for i > 0).
        Therefore, there exists a data configuration (a value for 'w') that forces sequentiality.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT, indicating DOFS (sequential).
        """
        print(
            "\n--- Running Test: Sequential Loop with symbolic max(i-w, 0) index (Expected: DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, N, w, A, B = (
            build_sequential_with_symbolic_max_index_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic) and w (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (sequential_with_symbolic_max_index_dofs) ---")
        print(smt_query)
        print("-----------------------------------------------------------------")

        # EXPECT: sat (True) - A data configuration (value for w) exists that forces
        # sequential execution across all adjacent iterations.
        result = solve_smt_string(smt_query, "sequential_with_symbolic_max_index_dofs")
        assert result, (
            "Expected sequential loop with symbolic max index to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nVerdict: PASSED. Sequential Loop with symbolic max(i-w, 0) index is DOFS (Sequential) as expected."
        )


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_sequential_with_symbolic_max_index_dofs_forall_bounds(self):
        """
        Test case for a Sequential Loop with max(i-w, 0) index, where w is a symbolic variable.
        for i = 2...N: A[i] = A[max(i-w, 0)] + B[i]
        Since 'w' is a symbolic variable, the SMT solver can choose a value for 'w' (e.g., w=1)
        that makes the loop sequential (A[i] = A[max(i-1, 0)] + B[i] becomes A[i] = A[i-1] + B[i] for i > 0).
        Therefore, there exists a data configuration (a value for 'w') that forces sequentiality.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT, indicating DOFS (sequential).
        """
        print(
            "\n--- Running Test: Sequential Loop with symbolic max(i-w, 0) index (Loop Bounds) (Expected: DOFS/Sequential) ---"
        )
        b_root_graph, loop_node, N, w, A, B = (
            build_sequential_with_symbolic_max_index_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic) and w (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print(
            "\n--- Generated SMT Query (sequential_with_symbolic_max_index_dofs_forall_bounds) ---"
        )
        print(smt_query)
        print("-----------------------------------------------------------------")

        # EXPECT: sat (True) - A data configuration (value for w) exists that forces
        # sequential execution across all adjacent iterations.
        result = solve_smt_string(
            smt_query, "sequential_with_symbolic_max_index_dofs_forall_bounds"
        )
        assert result, (
            "Expected sequential loop with symbolic max index (loop bounds) to be DOFS (sequential) but SMT solver returned UNSAT."
        )
        print(
            "\nVerdict: PASSED. Sequential Loop with symbolic max(i-w, 0) index (Loop Bounds) is DOFS (Sequential) as expected."
        )
