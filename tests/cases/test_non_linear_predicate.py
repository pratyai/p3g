from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import build_non_linear_predicate_graph


class TestNonLinearPredicate:
    def test_dofs(self):
        """
        Test case for a loop with a Non-linear Predicate:
        for i=0:N {
          if i*i <= N: A[i] = B[i] + C[i]  // Parallel part
          else: A[i] = A[i-1] + C[i]       // Sequential part
        }
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        Because the parallel branch (`A[i] = B[i] + C[i]`) can always be taken for some `k`
        (e.g., for `k=0`, `0*0 <= N` is always true for `N >= 0`), there is no data configuration
        that forces *all* adjacent iterations to be sequential.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        run_test_case(
            build_non_linear_predicate_graph,
            generate_smt_for_prove_exists_data_forall_iter_isdep,
            "non_linear_predicate_dofs",
            False,
        )

    def test_dofs_forall_bounds(self):
        """
        Test case for a loop with a Non-linear Predicate using loop bounds SMT:
        for i=0:N {
          if i*i <= N: A[i] = B[i] + C[i]  // Parallel part
          else: A[i] = A[i-1] + C[i]       // Sequential part
        }
        This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
        meaning it is parallelizable.
        Because the parallel branch (`A[i] = B[i] + C[i]`) can always be taken for some `k`
        (e.g., for `k=0`, `0*0 <= N` is always true for `N >= 0`), there is no data configuration
        that forces *all* adjacent iterations to be sequential.
        The SMT query should return UNSAT, indicating Not DOFS (parallel).
        """
        run_test_case(
            build_non_linear_predicate_graph,
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
            "non_linear_predicate_dofs_forall_bounds",
            False,
        )

    def test_find_dependency(self):
        """
        Test case for a loop with a Non-linear Predicate:
        for i=0:N {
          if i*i <= N: A[i] = B[i] + C[i]  // Parallel part
          else: A[i] = A[i-1] + C[i]       // Sequential part
        }
        This test uses the relaxed SMT query to find *any* dependency.
        A dependency exists if we can find a data configuration for N such that
        the sequential branch is taken for some j and k.
        The SMT query should return SAT.
        """
        run_test_case(
            build_non_linear_predicate_graph,
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
            "non_linear_predicate_find_dependency",
            True,
        )
