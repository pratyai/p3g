from pysmt.shortcuts import Int, GE

from p3g.smt import (
    exists_data_exists_bounds_forall_iter_isdep,
    exists_data_forall_bounds_forall_iter_isdep,
    exists_data_exists_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import build_array_reversal_graph


class TestArrayReversal:
    def test_dofs(self):
        """
        Test case for Array Reversal: for i = 0...N-1: swap(A[i], A[N-1-i]).
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        The SMT query asserts that the loop runs for at least two iterations.
        If N=2, the loop runs for k=0, j=1, and A[0] and A[1] are swapped, creating a dependency.
        If N is symbolic, the solver can pick N=2, which is sequential.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        run_test_case(
            build_array_reversal_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "array_reversal_dofs",
            True,
        )

    def test_high_N_dofs(self):
        """
        Test case for Array Reversal with N >= 3.
        This test expects the loop to be NOT Data-Oblivious Full Sequential (DOFS),
        meaning it is parallelizable.
        When N >= 3, for any k, the indices k and N-1-k are distinct and
        do not overlap with (k+1) and N-1-(k+1) for all valid k.
        This means there is no data configuration that forces sequential execution
        across all adjacent iterations.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        b_root_graph, loop_node, N, A_root = build_array_reversal_graph()
        run_test_case(
            lambda: (b_root_graph, loop_node, N, A_root),
            exists_data_exists_bounds_forall_iter_isdep,
            "array_reversal_high_N_dofs",
            False,
            extra_assertions=[GE(N, Int(3))],
        )

    def test_dofs_forall_bounds(self):
        """
        Test case for Array Reversal using generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        The SMT query asserts that the loop runs for at least two iterations.
        If N=2, the loop runs for k=0, j=1, and A[0] and A[1] are swapped, creating a dependency.
        If N is symbolic, the solver can pick N=2, which is sequential.
        The SMT query should return SAT, indicating DOFS (sequential).
        """
        run_test_case(
            build_array_reversal_graph,
            exists_data_forall_bounds_forall_iter_isdep,
            "array_reversal_dofs_forall_bounds",
            False,
        )

    def test_find_dependency(self):
        """
        Test case for Array Reversal: for i = 0...N-1: swap(A[i], A[N-1-i]).
        This test uses the relaxed SMT query to find *any* dependency.
        A dependency exists if we can find a data configuration for N such that
        the swap operation creates a dependency. For N=2, k=0, j=1, we have a dependency.
        The SMT query should return SAT.
        """
        run_test_case(
            build_array_reversal_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "array_reversal_find_dependency",
            True,
        )
