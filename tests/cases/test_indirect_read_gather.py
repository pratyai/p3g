from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import build_indirect_read_gather_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_indirect_read_gather_dofs(self):
        """
        Test case for Indirect Read (Gather) operation: for i = 1...N: A[i] = B[ IDX[i] ].
        This operation is generally parallelizable because writes to A[i] are independent
        of previous A values, and reads from B are indirect.
        There is no inherent data dependency between adjacent iterations that would force
        sequential execution for all data configurations.
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        print(
            "\n--- Running Test: Indirect Read (Gather) (Expected: Not DOFS/Parallel) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, IDX_root, IDX_val = (
            build_indirect_read_gather_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (indirect_read_gather_dofs) ---")
        print(smt_query)
        print("--------------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across all adjacent iterations.
        result = solve_smt_string(smt_query, "indirect_read_gather_dofs")
        assert not result, (
            "Expected indirect read (gather) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Indirect Read (Gather) is Not DOFS (Parallel) as expected."
        )


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_indirect_read_gather_dofs_forall_bounds(self):
        """
        Test case for Indirect Read (Gather) operation using loop bounds SMT: for i = 1...N: A[i] = B[ IDX[i] ].
        This operation is generally parallelizable because writes to A[i] are independent
        of previous A values, and reads from B are indirect.
        There is no inherent data dependency between adjacent iterations that would force
        sequential execution for all data configurations.
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        print(
            "\n--- Running Test: Indirect Read (Gather) (Loop Bounds) (Expected: Not DOFS/Parallel) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, IDX_root, IDX_val = (
            build_indirect_read_gather_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (indirect_read_gather_dofs_forall_bounds) ---")
        print(smt_query)
        print("--------------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across all adjacent iterations.
        result = solve_smt_string(smt_query, "indirect_read_gather_dofs_forall_bounds")
        assert not result, (
            "Expected indirect read (gather) (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Indirect Read (Gather) (Loop Bounds) is Not DOFS (Parallel) as expected."
        )
