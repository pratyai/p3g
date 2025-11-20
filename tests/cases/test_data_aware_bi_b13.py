from pysmt.shortcuts import Int, GE

from p3g.smt import (
    exists_data_exists_bounds_forall_iter_isdep,
    exists_data_forall_bounds_forall_iter_isdep,
    exists_data_exists_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import build_data_aware_bi_b13_graph


class TestDataAwareBiB13:
    def test_dofs(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        For example, if B[i] = 1 for all i, and B[13] = 0, then B[i] - B[13] > 0 is always true,
        and the loop becomes A[i] = A[i-1], which is sequential.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        run_test_case(
            build_data_aware_bi_b13_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "data_aware_bi_b13_dofs",
            True,
        )

    def test_high_N_dofs(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
        This test adds an assertion N >= 15.
        When N >= 15, the loop includes k=13. For k=13, the condition B[13] - B[13] > 0 is false,
        meaning the assignment A[13] = A[12] is skipped.
        Since there's at least one iteration (k=13) where the dependency is not guaranteed,
        the loop is Not Data-Oblivious Full Sequential (Not DOFS), meaning it is parallelizable.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        b_root_graph, loop_node, N, A_root, B_root, B_val, const_idx = (
            build_data_aware_bi_b13_graph()
        )
        run_test_case(
            lambda: (b_root_graph, loop_node, N, A_root, B_root, B_val, const_idx),
            exists_data_exists_bounds_forall_iter_isdep,
            "data_aware_bi_b13_high_N_dofs",
            False,
            extra_assertions=[GE(N, Int(15))],
        )

    def test_dofs_forall_bounds(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        For example, if B[i] = 1 for all i, and B[13] = 0, then B[i] - B[13] > 0 is always true,
        and the loop becomes A[i] = A[i-1], which is sequential.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        run_test_case(
            build_data_aware_bi_b13_graph,
            exists_data_forall_bounds_forall_iter_isdep,
            "data_aware_bi_b13_dofs_forall_bounds",
            False,
        )

    def test_find_dependency(self):
        """
        Test case for a Data-Aware loop: for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
        This test uses the relaxed SMT query to find *any* dependency.
        A dependency exists if we can find a data configuration for B such that
        the sequential branch is taken for some j and k.
        The SMT query should return SAT.
        """
        run_test_case(
            build_data_aware_bi_b13_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "data_aware_bi_b13_find_dependency",
            True,
        )
