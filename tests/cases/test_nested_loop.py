from pysmt.shortcuts import Symbol, INT, GT, Int

from p3g.smt import (
    exists_data_exists_bounds_forall_iter_isdep,
    exists_data_forall_bounds_forall_iter_isdep,
    exists_data_exists_bounds_forall_iter_isindep,
    exists_data_forall_bounds_forall_iter_isindep,
    forall_data_forall_bounds_forall_iter_isindep,
    exists_data_exists_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import (
    build_nested_loop_outer_dofs_graph,
    build_nested_loop_inner_dofs_graph,
)

M = Symbol("M", INT)
extra_assertions = [GT(M, Int(0))]


class TestNestedLoop:
    def test_outer_dofs(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        The outer loop (over 'i') has a true data dependency (A[i,j] depends on A[i-1,j]),
        making it Data-Oblivious Full Sequential (DOFS).
        The inner loop (over 'j') has no self-dependency, making it Not DOFS (parallelizable).
        """
        # run_test_case(
        #     build_nested_loop_outer_dofs_graph,
        #     generate_smt_for_prove_exists_data_forall_iter_isdep,
        #     "nested_loop_outer_dofs_inner",
        #     False,
        #     loop_node_index=2,
        # )
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "nested_loop_outer_dofs_outer",
            True,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_inner_dofs(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        The outer loop (over 'i') has no self-dependency, making it Not DOFS (parallelizable).
        The inner loop (over 'j') has a true data dependency (A[i,j] depends on A[i,j-1]),
        making it Data-Oblivious Full Sequential (DOFS).
        """
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "nested_loop_inner_dofs_inner",
            True,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "nested_loop_inner_dofs_outer",
            False,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_outer_dofs_forall_bounds(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS using loop bounds SMT:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]
        """
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            exists_data_forall_bounds_forall_iter_isdep,
            "nested_loop_outer_dofs_inner_forall_bounds",
            False,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            exists_data_forall_bounds_forall_iter_isdep,
            "nested_loop_outer_dofs_outer_forall_bounds",
            True,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_inner_dofs_forall_bounds(self):
        """
        Test case for a Nested Loop with inner loop DOFS using loop bounds SMT:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]
        """
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            exists_data_forall_bounds_forall_iter_isdep,
            "nested_loop_inner_dofs_inner_forall_bounds",
            True,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            exists_data_forall_bounds_forall_iter_isdep,
            "nested_loop_inner_dofs_outer_forall_bounds",
            False,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_outer_dofi(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        The outer loop is sequential, so it should be NOT DOFI.
        The inner loop is parallel, so it should be DOFI.
        """
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            exists_data_exists_bounds_forall_iter_isindep,
            "nested_loop_outer_dofs_inner_dofi",
            True,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            exists_data_exists_bounds_forall_iter_isindep,
            "nested_loop_outer_dofs_outer_dofi",
            False,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_inner_dofi(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        The outer loop is parallel, so it should be DOFI.
        The inner loop is sequential, so it should be NOT DOFI.
        """
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            exists_data_exists_bounds_forall_iter_isindep,
            "nested_loop_inner_dofs_inner_dofi",
            False,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            exists_data_exists_bounds_forall_iter_isindep,
            "nested_loop_inner_dofs_outer_dofi",
            True,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_outer_dofi_forall_bounds(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        The outer loop is sequential, so it should be NOT DOFI.
        The inner loop is parallel, so it should be DOFI.
        This test uses universally quantified loop bounds.
        """
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            exists_data_forall_bounds_forall_iter_isindep,
            "nested_loop_outer_dofs_inner_dofi_forall_bounds",
            True,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            exists_data_forall_bounds_forall_iter_isindep,
            "nested_loop_outer_dofs_outer_dofi_forall_bounds",
            False,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_inner_dofi_forall_bounds(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        The outer loop is parallel, so it should be DOFI.
        The inner loop is sequential, so it should be NOT DOFI.
        This test uses universally quantified loop bounds.
        """
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            exists_data_forall_bounds_forall_iter_isindep,
            "nested_loop_inner_dofs_inner_dofi_forall_bounds",
            False,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            exists_data_forall_bounds_forall_iter_isindep,
            "nested_loop_inner_dofs_outer_dofi_forall_bounds",
            True,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_outer_forall_data_forall_bounds(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        The outer loop is sequential, so it should be NOT DOFI.
        The inner loop is parallel, so it should be DOFI.
        This test uses universally quantified data and loop bounds.
        """
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            forall_data_forall_bounds_forall_iter_isindep,
            "nested_loop_outer_dofs_inner_forall_data_forall_bounds",
            True,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            forall_data_forall_bounds_forall_iter_isindep,
            "nested_loop_outer_dofs_outer_forall_data_forall_bounds",
            False,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_inner_forall_data_forall_bounds(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        The outer loop is parallel, so it should be DOFI.
        The inner loop is sequential, so it should be NOT DOFI.
        This test uses universally quantified data and loop bounds.
        """
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            forall_data_forall_bounds_forall_iter_isindep,
            "nested_loop_inner_dofs_inner_forall_data_forall_bounds",
            False,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            forall_data_forall_bounds_forall_iter_isindep,
            "nested_loop_inner_dofs_outer_forall_data_forall_bounds",
            True,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_outer_find_dependency(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        This test uses the relaxed SMT query to find *any* dependency.
        The outer loop has a RAW dependency, so a dependency should be found.
        The SMT query should return SAT.
        """
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "nested_loop_outer_dofs_find_dependency",
            True,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_outer_inner_find_dependency(self):
        """
        Test case for a Nested Loop where the OUTER loop is DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

        This test uses the relaxed SMT query to find *any* dependency.
        The inner loop is fully parallel, so no dependency should be found.
        The SMT query should return UNSAT.
        """
        run_test_case(
            build_nested_loop_outer_dofs_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "nested_loop_outer_dofs_inner_find_dependency",
            False,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )

    def test_inner_find_dependency(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        This test uses the relaxed SMT query to find *any* dependency.
        The outer loop is fully parallel, so no dependency should be found.
        The SMT query should return UNSAT.
        """
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "nested_loop_inner_dofs_find_dependency",
            False,
            loop_node_index=1,
            extra_assertions=extra_assertions,
        )

    def test_inner_inner_find_dependency(self):
        """
        Test case for a Nested Loop with inner loop DOFS:
        for i = 1...N:
          for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

        This test uses the relaxed SMT query to find *any* dependency.
        The inner loop has a RAW dependency, so a dependency should be found.
        The SMT query should return SAT.
        """
        run_test_case(
            build_nested_loop_inner_dofs_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "nested_loop_inner_dofs_inner_find_dependency",
            True,
            loop_node_index=2,
            extra_assertions=extra_assertions,
        )
