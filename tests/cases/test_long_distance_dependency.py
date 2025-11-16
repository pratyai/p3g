from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import build_long_distance_dependency_graph


class TestLongDistanceDependency:
    def test_dofs(self):
        """
        Test case for a loop with long-distance dependency: for i = 2...N: A[i] = A[max(i-10, 0)] + B[i].
        The dependency is A[i] <- A[max(i-10, 0)]. Due to the 'max(i-10, 0)' term,
        A[i] typically depends on a value far removed from A[i-1].
        This means there is no inherent data dependency between *adjacent* iterations (k and k+1)
        that would force sequential execution for all data configurations.
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        run_test_case(
            build_long_distance_dependency_graph,
            generate_smt_for_prove_exists_data_forall_iter_isdep,
            "long_distance_dependency_dofs",
            False,
        )

    def test_dofs_forall_bounds(self):
        """
        Test case for a loop with long-distance dependency using loop bounds SMT:
        for i = 2...N: A[i] = A[max(i-10, 0)] + B[i].
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        run_test_case(
            build_long_distance_dependency_graph,
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
            "long_distance_dependency_dofs_forall_bounds",
            False,
        )

    def test_find_dependency(self):
        """
        Test case for a loop with long-distance dependency: for i = 2...N: A[i] = A[max(i-10, 0)] + B[i].
        This test uses the relaxed SMT query to find *any* dependency.
        A dependency exists if we can find a data configuration for N such that
        the loop has a dependency. For example, if k=10, j=20, then A[20] depends on A[10].
        The SMT query should return SAT.
        """
        run_test_case(
            build_long_distance_dependency_graph,
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
            "long_distance_dependency_find_dependency",
            True,
        )
