from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_forall_iter_isindep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import build_sequential_loop_graph


class TestSequentialLoop:
    def test_sequential_loop_dofs(self):
        """
        Test case for a Sequential Loop: for i = 2...N: A[i] = A[i-1] + B[i].
        This loop has a Read-After-Write (RAW) dependency: A[i] reads A[i-1],
        which was written in the previous iteration. This dependency exists for all
        iterations in the loop range.
        Therefore, the loop is inherently sequential.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT, indicating DOFS (sequential).
        """
        run_test_case(
            build_sequential_loop_graph,
            generate_smt_for_prove_exists_data_forall_iter_isdep,
            "sequential_loop_dofs",
            True,
        )

    def test_sequential_loop_dofs_forall_bounds(self):
        """
        Test case for a Sequential Loop using loop bounds SMT: for i = 2...N: A[i] = A[i-1] + B[i].
        This loop has a Read-After-Write (RAW) dependency: A[i] reads A[i-1],
        which was written in the previous iteration. This dependency exists for all
        iterations in the loop range.
        Therefore, the loop is inherently sequential.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT, indicating DOFS (sequential).
        """
        run_test_case(
            build_sequential_loop_graph,
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
            "sequential_loop_dofs_forall_bounds",
            True,
        )

    def test_sequential_loop_dofi(self):
        """
        Test case for a Sequential Loop: for i = 2...N: A[i] = A[i-1] + B[i].
        This loop has a Read-After-Write (RAW) dependency.
        This test expects the loop to be Not Data-Oblivious Fully Independent (Not DOFI),
        meaning it is not parallelizable.
        The SMT query should return UNSAT, indicating Not DOFI (sequential).
        """
        run_test_case(
            build_sequential_loop_graph,
            generate_smt_for_prove_exists_data_forall_iter_isindep,
            "sequential_loop_dofi",
            False,
        )

    def test_sequential_loop_dofi_forall_bounds(self):
        """
        Test case for a Sequential Loop using loop bounds SMT: for i = 2...N: A[i] = A[i-1] + B[i].
        This loop has a Read-After-Write (RAW) dependency.
        This test expects the loop to be Not Data-Oblivious Fully Independent (Not DOFI),
        meaning it is not parallelizable, even with symbolic loop bounds.
        The SMT query should return UNSAT, indicating Not DOFI (sequential).
        """
        run_test_case(
            build_sequential_loop_graph,
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
            "sequential_loop_dofi_forall_bounds",
            False,
        )

    def test_sequential_loop_forall_data_forall_bounds(self):
        """
        Test case for a Sequential Loop using SMT with universally quantified data and loop bounds:
        for i = 2...N: A[i] = A[i-1] + B[i].
        This loop has a Read-After-Write (RAW) dependency.
        This test expects the loop to be Not Data-Oblivious Fully Independent (Not DOFI),
        meaning it is not parallelizable for all data configurations and all symbolic loop bounds.
        The SMT query should return UNSAT, indicating Not DOFI (sequential).
        """
        run_test_case(
            build_sequential_loop_graph,
            generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
            "sequential_loop_forall_data_forall_bounds",
            False,
        )

    def test_sequential_loop_find_dependency(self):
        """
        Test case for a Sequential Loop: for i = 2...N: A[i] = A[i-1] + B[i].
        This test uses the relaxed SMT query to find *any* dependency.
        This loop has a RAW dependency, so a dependency should be found.
        The SMT query should return SAT.
        """
        run_test_case(
            build_sequential_loop_graph,
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
            "sequential_loop_find_dependency",
            True,
        )
