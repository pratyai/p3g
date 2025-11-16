from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_forall_iter_isindep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import build_parallel_loop_graph


class TestParallelLoop:
    def test_parallel_loop_dofs(self):
        """
        Test case for a Parallel Loop: for i in 0:n { a[i] = b[i] + c[i] }.
        Each iteration of this loop is independent, as it only reads from B and C
        and writes to A at the current index 'i'. There are no dependencies
        between adjacent iterations that would force sequential execution.
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        run_test_case(
            build_parallel_loop_graph,
            generate_smt_for_prove_exists_data_forall_iter_isdep,
            "parallel_loop_dofs",
            False,
        )

    def test_parallel_loop_dofs_forall_bounds(self):
        """
        Test case for a Parallel Loop using loop bounds SMT: for i in 0:n { a[i] = b[i] + c[i] }.
        Each iteration of this loop is independent, as it only reads from B and C
        and writes to A at the current index 'i'. There are no dependencies
        between adjacent iterations that would force sequential execution.
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        run_test_case(
            build_parallel_loop_graph,
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
            "parallel_loop_dofs_forall_bounds",
            False,
        )

    def test_parallel_loop_dofi(self):
        """
        Test case for a Parallel Loop: for i in 0:n { a[i] = b[i] + c[i] }.
        Each iteration of this loop is independent.
        This test expects the loop to be Data-Oblivious Fully Independent (DOFI),
        meaning it is parallelizable.
        The SMT query should return SAT, indicating DOFI (parallel).
        """
        run_test_case(
            build_parallel_loop_graph,
            generate_smt_for_prove_exists_data_forall_iter_isindep,
            "parallel_loop_dofi",
            True,
        )

    def test_parallel_loop_dofi_forall_bounds(self):
        """
        Test case for a Parallel Loop using loop bounds SMT: for i in 0:n { a[i] = b[i] + c[i] }.
        Each iteration of this loop is independent.
        This test expects the loop to be Data-Oblivious Fully Independent (DOFI),
        meaning it is parallelizable, even with symbolic loop bounds.
        The SMT query should return SAT, indicating DOFI (parallel).
        """
        run_test_case(
            build_parallel_loop_graph,
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
            "parallel_loop_dofi_forall_bounds",
            True,
        )

    def test_parallel_loop_forall_data_forall_bounds(self):
        """
        Test case for a Parallel Loop using SMT with universally quantified data and loop bounds:
        for i in 0:n { a[i] = b[i] + c[i] }.
        Each iteration of this loop is independent.
        This test expects the loop to be Data-Oblivious Fully Independent (DOFI),
        meaning it is parallelizable for all data configurations and all symbolic loop bounds.
        The SMT query should return SAT, indicating DOFI (parallel).
        """
        run_test_case(
            build_parallel_loop_graph,
            generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
            "parallel_loop_forall_data_forall_bounds",
            True,
        )

    def test_parallel_loop_find_dependency(self):
        """
        Test case for a Parallel Loop: for i in 0:n { a[i] = b[i] + c[i] }.
        This test uses the relaxed SMT query to find *any* dependency.
        This loop is fully parallel, so no dependency should be found.
        The SMT query should return UNSAT.
        """
        run_test_case(
            build_parallel_loop_graph,
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
            "parallel_loop_find_dependency",
            False,
        )
