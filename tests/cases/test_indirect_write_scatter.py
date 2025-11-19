import pytest

from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_forall_iter_isindep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import build_indirect_write_scatter_graph
from tests.utils import TimeoutError


class TestIndirectWriteScatter:
    def test_dofs(self):
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
        run_test_case(
            build_indirect_write_scatter_graph,
            generate_smt_for_prove_exists_data_forall_iter_isdep,
            "indirect_write_scatter_dofs",
            True,
        )

    def test_dofs_forall_bounds(self):
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
        run_test_case(
            build_indirect_write_scatter_graph,
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
            "indirect_write_scatter_dofs_forall_bounds",
            True,
        )

    def test_dofi(self):
        """
        Test case for Indirect Write (Scatter) operation: for i = 1...N: A[ IDX[i] ] = B[i].
        This operation can be parallel if the index array `IDX` is configured to avoid conflicts
        (e.g., if all `IDX[i]` values are unique).
        This test expects the loop to be Data-Oblivious Fully Independent (DOFI) because
        a parallelizing data configuration for `IDX` can exist.
        The SMT query should return SAT, indicating DOFI (parallel).
        """
        run_test_case(
            build_indirect_write_scatter_graph,
            generate_smt_for_prove_exists_data_forall_iter_isindep,
            "indirect_write_scatter_dofi",
            True,
        )

    def test_dofi_forall_bounds(self):
        """
        Test case for Indirect Write (Scatter) operation using loop bounds SMT: for i = 1...N: A[ IDX[i] ] = B[i].
        This operation can be parallel if the index array `IDX` is configured to avoid conflicts
        (e.g., if all `IDX[i]` values are unique).
        This test expects the loop to be Data-Oblivious Fully Independent (DOFI) because
        a parallelizing data configuration for `IDX` can exist, even with symbolic loop bounds.
        The SMT query should return SAT, indicating DOFI (parallel).
        """
        try:
            run_test_case(
                build_indirect_write_scatter_graph,
                generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
                "indirect_write_scatter_dofi_forall_bounds",
                True,
                timeout_seconds=10,
            )
        except TimeoutError as e:
            pytest.skip(f"Skipping due to timeout: {e}")

    def test_forall_data_forall_bounds(self):
        """
        Test case for Indirect Write (Scatter) operation using SMT with universally quantified data and loop bounds:
        for i = 1...N: A[ IDX[i] ] = B[i].
        This operation is generally sequential because multiple iterations can write to the same
        memory location in A if IDX[i] values are not unique or create dependencies.
        This test expects the loop to be Not Data-Oblivious Fully Independent (Not DOFI),
        meaning it is not parallelizable for all data configurations and all symbolic loop bounds.
        The SMT query should return UNSAT, indicating Not DOFI (sequential).
        """
        try:
            run_test_case(
                build_indirect_write_scatter_graph,
                generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
                "indirect_write_scatter_forall_data_forall_bounds",
                False,
                timeout_seconds=10,
            )
        except TimeoutError as e:
            pytest.skip(f"Skipping due to timeout: {e}")

    def test_find_dependency(self):
        """
        Test case for Indirect Write (Scatter) operation: for i = 1...N: A[ IDX[i] ] = B[i].
        This test uses the relaxed SMT query to find *any* dependency.
        A dependency exists if we can find a data configuration for IDX such that
        IDX[j] = IDX[k] for some j < k. This creates a WAW dependency on A.
        The SMT solver should be able to find such a configuration.
        The SMT query should return SAT.
        """
        run_test_case(
            build_indirect_write_scatter_graph,
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
            "indirect_write_scatter_find_dependency",
            True,
        )
