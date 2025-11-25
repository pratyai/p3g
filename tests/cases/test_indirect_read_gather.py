from p3g.smt import (
    exists_data_exists_bounds_forall_iter_isdep,
    exists_data_exists_bounds_forall_iter_isindep,
    exists_data_forall_bounds_forall_iter_isindep,
    forall_data_forall_bounds_forall_iter_isindep,
    exists_data_exists_bounds_exists_iter_isdep,
)
from p3g.smt_v2 import exists_data_forall_bounds_forall_iters_chained
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import build_indirect_read_gather_graph


class TestIndirectReadGather:
    def test_dofs(self):
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
        run_test_case(
            build_indirect_read_gather_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "indirect_read_gather_dofs",
            False,
        )

    def test_dofs_forall_bounds(self):
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
        run_test_case(
            build_indirect_read_gather_graph,
            exists_data_forall_bounds_forall_iters_chained,
            "indirect_read_gather_dofs_forall_bounds",
            False,
        )

    def test_dofi(self):
        """
        Test case for Indirect Read (Gather) operation: for i = 1...N: A[i] = B[ IDX[i] ].
        This operation is generally parallelizable.
        This test expects the loop to be Data-Oblivious Fully Independent (DOFI),
        meaning it is parallelizable.
        The SMT query should return SAT, indicating DOFI (parallel).
        """
        run_test_case(
            build_indirect_read_gather_graph,
            exists_data_exists_bounds_forall_iter_isindep,
            "indirect_read_gather_dofi",
            True,
        )

    def test_dofi_forall_bounds(self):
        """
        Test case for Indirect Read (Gather) operation using loop bounds SMT: for i = 1...N: A[i] = B[ IDX[i] ].
        This operation is generally parallelizable.
        This test expects the loop to be Data-Oblivious Fully Independent (DOFI),
        meaning it is parallelizable, even with symbolic loop bounds.
        The SMT query should return SAT, indicating DOFI (parallel).
        """
        run_test_case(
            build_indirect_read_gather_graph,
            exists_data_forall_bounds_forall_iter_isindep,
            "indirect_read_gather_dofi_forall_bounds",
            True,
        )

    def test_forall_data_forall_bounds(self):
        """
        Test case for Indirect Read (Gather) operation using SMT with universally quantified data and loop bounds:
        for i = 1...N: A[i] = B[ IDX[i] ].
        This operation is generally parallelizable.
        This test expects the loop to be Data-Oblivious Fully Independent (DOFI),
        meaning it is parallelizable for all data configurations and all symbolic loop bounds.
        The SMT query should return SAT, indicating DOFI (parallel).
        """
        run_test_case(
            build_indirect_read_gather_graph,
            forall_data_forall_bounds_forall_iter_isindep,
            "indirect_read_gather_forall_data_forall_bounds",
            True,
        )

    def test_find_dependency(self):
        """
        Test case for Indirect Read (Gather) operation: for i = 1...N: A[i] = B[ IDX[i] ].
        This test uses the relaxed SMT query to find *any* dependency.
        This loop is fully parallel, so no dependency should be found.
        The SMT query should return UNSAT.
        """
        run_test_case(
            build_indirect_read_gather_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "indirect_read_gather_find_dependency",
            False,
        )
