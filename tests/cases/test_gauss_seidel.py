from p3g.smt import (
    exists_data_exists_bounds_forall_iter_isdep,
    exists_data_forall_bounds_forall_iter_isdep,
    exists_data_exists_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import (
    build_gauss_seidel_red_graph,
    build_gauss_seidel_black_graph,
    build_gauss_seidel_traditional_graph,
)


class TestGaussSeidel:
    def test_red_dofs(self):
        """
        Test case for Gauss-Seidel Red Pass (1D).
        Expected to be Not Data-Oblivious Full Sequential (Not DOFS), meaning parallelizable.

        // Red Pass (odd indices - parallel)
        for i = 1, 3, 5, ...:
            A[i] = A[i-1] + A[i+1]
        """
        run_test_case(
            build_gauss_seidel_red_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "gauss_seidel_red_dofs",
            False,
        )

    def test_black_dofs(self):
        """
        Test case for Gauss-Seidel Black Pass (1D).
        Expected to be Not Data-Oblivious Full Sequential (Not DOFS), meaning parallelizable.

        // Black Pass (even indices - parallel)
        for i = 2, 4, 6, ...:
            A[i] = A[i-1] + A[i+1]
        """
        run_test_case(
            build_gauss_seidel_black_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "gauss_seidel_black_dofs",
            False,
        )

    def test_traditional_dofs(self):
        """
        Test case for the Traditional 1D Gauss-Seidel loop.
        for i = 1 to N-1:
          A[i] = A[i-1] + A[i+1]

        This loop is inherently sequential because A[i] depends on A[i-1],
        which was just computed in the current iteration. This creates a
        Read-After-Write (RAW) dependency between adjacent iterations.
        Therefore, this test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT.
        """
        run_test_case(
            build_gauss_seidel_traditional_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "gauss_seidel_traditional_dofs",
            True,
        )

    def test_red_dofs_forall_bounds(self):
        """
        Test case for Gauss-Seidel Red Pass (1D) using loop bounds SMT.
        Expected to be Not Data-Oblivious Full Sequential (Not DOFS), meaning parallelizable.
        """
        run_test_case(
            build_gauss_seidel_red_graph,
            exists_data_forall_bounds_forall_iter_isdep,
            "gauss_seidel_red_dofs_forall_bounds",
            False,
        )

    def test_black_dofs_forall_bounds(self):
        """
        Test case for Gauss-Seidel Black Pass (1D) using loop bounds SMT.
        Expected to be Not Data-Oblivious Full Sequential (Not DOFS), meaning parallelizable.
        """
        run_test_case(
            build_gauss_seidel_black_graph,
            exists_data_forall_bounds_forall_iter_isdep,
            "gauss_seidel_black_dofs_forall_bounds",
            False,
        )

    def test_traditional_dofs_forall_bounds(self):
        """
        Test case for the Traditional 1D Gauss-Seidel loop using loop bounds SMT.
        This loop is inherently sequential because A[i] depends on A[i-1],
        which was just computed in the current iteration.
        """
        run_test_case(
            build_gauss_seidel_traditional_graph,
            exists_data_forall_bounds_forall_iter_isdep,
            "gauss_seidel_traditional_dofs_forall_bounds",
            True,
        )

    def test_red_find_dependency(self):
        """
        Test case for Gauss-Seidel Red Pass (1D).
        This test uses the relaxed SMT query to find *any* dependency.
        This loop is fully parallel, so no dependency should be found.
        """
        run_test_case(
            build_gauss_seidel_red_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "gauss_seidel_red_find_dependency",
            False,
        )

    def test_black_find_dependency(self):
        """
        Test case for Gauss-Seidel Black Pass (1D).
        This test uses the relaxed SMT query to find *any* dependency.
        This loop is fully parallel, so no dependency should be found.
        """
        run_test_case(
            build_gauss_seidel_black_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "gauss_seidel_black_find_dependency",
            False,
        )

    def test_traditional_find_dependency(self):
        """
        Test case for the Traditional 1D Gauss-Seidel loop.
        This test uses the relaxed SMT query to find *any* dependency.
        This loop has a RAW dependency, so a dependency should be found.
        """
        run_test_case(
            build_gauss_seidel_traditional_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "gauss_seidel_traditional_find_dependency",
            True,
        )
