from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import (
    build_non_linear_access_graph,
    build_non_linear_access_sequential_graph,
)


class TestNonLinearAccess:
    def test_dofs(self):
        """
        Test case for a loop with a Non-linear Array Access:
        for i=0:N: A[i*i] = B[i] + C[i]
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        The non-linear access pattern `i*i` ensures that for `i > 0`, `i*i` and `(i+1)*(i+1)`
        are distinct and sufficiently far apart to avoid adjacent iteration dependencies.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        run_test_case(
            build_non_linear_access_graph,
            generate_smt_for_prove_exists_data_forall_iter_isdep,
            "non_linear_access_dofs",
            False,
        )

    def test_sequential_dofs(self):
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
        run_test_case(
            build_non_linear_access_sequential_graph,
            generate_smt_for_prove_exists_data_forall_iter_isdep,
            "non_linear_access_sequential_dofs",
            True,
        )

    def test_dofs_forall_bounds(self):
        """
        Test case for a loop with a Non-linear Array Access using loop bounds SMT:
        for i=0:N: A[i*i] = B[i] + C[i]
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        The non-linear access pattern `i*i` ensures that for `i > 0`, `i*i` and `(i+1)*(i+1)`
        are distinct and sufficiently far apart to avoid adjacent iteration dependencies.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        run_test_case(
            build_non_linear_access_graph,
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
            "non_linear_access_dofs_forall_bounds",
            False,
        )

    def test_sequential_dofs_forall_bounds(self):
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
        run_test_case(
            build_non_linear_access_sequential_graph,
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
            "non_linear_access_sequential_dofs_forall_bounds",
            True,
        )

    def test_find_dependency(self):
        """
        Test case for a loop with a Non-linear Array Access:
        for i=0:N: A[i*i] = B[i] + C[i]
        This test uses the relaxed SMT query to find *any* dependency.
        This loop is fully parallel, so no dependency should be found.
        """
        run_test_case(
            build_non_linear_access_graph,
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
            "non_linear_access_find_dependency",
            False,
        )

    def test_sequential_find_dependency(self):
        """
        Test case for a loop with a Non-linear Array Access that is sequential:
        for i = 1...N: A[i*i] = A[(i-1)*(i-1)] + B[i]
        This test uses the relaxed SMT query to find *any* dependency.
        This loop has a RAW dependency, so a dependency should be found.
        """
        run_test_case(
            build_non_linear_access_sequential_graph,
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
            "non_linear_access_sequential_find_dependency",
            True,
        )
