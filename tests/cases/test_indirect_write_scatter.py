from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_forall_iter_isindep,
)
from tests.cases.graph_definitions import build_indirect_write_scatter_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
    def test_indirect_write_scatter_dofs(self):
        """
        Test case for Indirect Write (Scatter) operation: for i = 1...N: A[ IDX[i] ] = B[i].
        This operation is generally sequential because multiple iterations can write to the same
        memory location in A if IDX[i] values are not unique or create dependencies.
        For example, if IDX[i] = 5 for all i, then all iterations write to A[5], creating a WAW dependency.
        However, the SMT query is designed to prove *existence* of a sequentializing data configuration.
        If the loop is *always* sequential (DOFS), the SMT solver should return SAT.
        If the loop is *not always* sequential (Not DOFS / Parallelizable), the SMT solver should return UNSAT.

        The current test expects the loop to be Not DOFS (parallelizable) for *some* data configurations,
        meaning it's not *always* sequential. This implies the SMT solver should return UNSAT.
        """
        print(
            "\n--- Running Test: Indirect Write (Scatter) (Expected: Not DOFS/Parallel) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, IDX_root, IDX_val = (
            build_indirect_write_scatter_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (indirect_write_scatter_dofs) ---")
        print(smt_query)
        print("---------------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across *all* adjacent iterations. This means it's parallelizable.
        result = solve_smt_string(smt_query, "indirect_write_scatter_dofs")
        assert not result, (
            "Expected indirect write (scatter) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Indirect Write (Scatter) is Not DOFS (Parallel) as expected."
        )


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_indirect_write_scatter_dofs_forall_bounds(self):
        """
        Test case for Indirect Write (Scatter) operation using loop bounds SMT: for i = 1...N: A[ IDX[i] ] = B[i].
        This operation is generally sequential because multiple iterations can write to the same
        memory location in A if IDX[i] values are not unique or create dependencies.
        For example, if IDX[i] = 5 for all i, then all iterations write to A[5], creating a WAW dependency.
        However, the SMT query is designed to prove *existence* of a sequentializing data configuration.
        If the loop is *always* sequential (DOFS), the SMT solver should return SAT.
        If the loop is *not always* sequential (Not DOFS / Parallelizable), the SMT solver should return UNSAT.

        The current test expects the loop to be Not DOFS (parallelizable) for *some* data configurations,
        meaning it's not *always* sequential. This implies the SMT solver should return UNSAT.
        """
        print(
            "\n--- Running Test: Indirect Write (Scatter) (Loop Bounds) (Expected: Not DOFS/Parallel) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, IDX_root, IDX_val = (
            build_indirect_write_scatter_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print(
            "\n--- Generated SMT Query (indirect_write_scatter_dofs_forall_bounds) ---"
        )
        print(smt_query)
        print("---------------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across *all* adjacent iterations. This means it's parallelizable.
        result = solve_smt_string(
            smt_query, "indirect_write_scatter_dofs_forall_bounds"
        )
        assert not result, (
            "Expected indirect write (scatter) (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Indirect Write (Scatter) (Loop Bounds) is Not DOFS (Parallel) as expected."
        )


class TestProveExistsDataForallIterIsindep:
    def test_indirect_write_scatter_dofi(self):
        """
        Test case for Indirect Write (Scatter) operation: for i = 1...N: A[ IDX[i] ] = B[i].
        This operation can be parallel if the index array `IDX` is configured to avoid conflicts
        (e.g., if all `IDX[i]` values are unique).
        This test expects the loop to be Data-Oblivious Fully Independent (DOFI) because
        a parallelizing data configuration for `IDX` can exist.
        The SMT query should return SAT, indicating DOFI (parallel).
        """
        print(
            "\n--- Running Test: Indirect Write (Scatter) (Expected: DOFI/Parallel) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, IDX_root, IDX_val = (
            build_indirect_write_scatter_graph()
        )

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isindep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (indirect_write_scatter_dofi) ---")
        print(smt_query)
        print("---------------------------------------------------")

        # EXPECT: sat (True) - A data configuration for IDX exists that makes the loop parallel.
        result = solve_smt_string(smt_query, "indirect_write_scatter_dofi")
        assert result, (
            "Expected indirect write (scatter) to be DOFI (parallel) but SMT solver returned UNSAT."
        )
        print(
            "\nVerdict: PASSED. Indirect Write (Scatter) is DOFI (Parallel) as expected."
        )
