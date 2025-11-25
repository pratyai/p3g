from p3g.smt import (
    exists_data_exists_bounds_forall_iter_isdep,
    exists_data_exists_bounds_exists_iter_isdep,
)
from p3g.smt_v2 import exists_data_forall_bounds_forall_iters_chained
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import build_data_aware_bi_graph


class TestDataAwareBI:
    def test_dofs(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] > 0) then A[i] = A[i-1].
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        If all B[i] > 0, then A[i] = A[i-1] always executes, creating a sequential dependency.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        run_test_case(
            build_data_aware_bi_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "data_aware_bi_dofs",
            True,
        )

    def test_dofs_forall_bounds(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] > 0) then A[i] = A[i-1].
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        If all B[i] > 0, then A[i] = A[i-1] always executes, creating a sequential dependency.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        run_test_case(
            build_data_aware_bi_graph,
            exists_data_forall_bounds_forall_iters_chained,
            "data_aware_bi_dofs_forall_bounds",
            True,
        )

    def test_find_dependency(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] > 0) then A[i] = A[i-1].
        This test uses the relaxed SMT query to find *any* dependency.
        A dependency exists if we can find a data configuration for B such that
        the sequential branch is taken for some j and k.
        The SMT query should return SAT.
        """
        run_test_case(
            build_data_aware_bi_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "data_aware_bi_find_dependency",
            True,
        )
