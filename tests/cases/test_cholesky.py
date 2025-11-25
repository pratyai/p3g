from p3g.smt import (
    exists_data_exists_bounds_forall_iter_isdep,
    exists_data_exists_bounds_exists_iter_isdep,
)
from p3g.smt_v2 import exists_data_forall_bounds_forall_iters_chained
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import (
    build_cholesky_full_kernel_graph,
    build_cholesky_sequential_graph,
)


class TestCholesky:
    def test_sequential_dofs(self):
        """
        Cholesky Decomposition-like kernel (fully sequential)
        for i = 2...N:
          for j = 2...i:
            L[i, j] = L[i, j-1] + L[j-1, j-1]

        # Actual Cholesky inner kernel (simplified for L[i,j] calculation):
        # L[i,j] = (A[i,j] - sum_{k=0}^{j-1} L[i,k] * L[j,k]) / L[j,j]
        # This test models a simplified dependency pattern found in such kernels.
        """
        # Justification: This test case checks the inner loop (j loop) of the Cholesky sequential graph.
        # Expectation: The inner loop exhibits a true Read-After-Write (RAW) dependency
        # on `L[i, j-1]`. This loop-carried dependency forces sequential execution.
        # Therefore, it must be Data-Oblivious Full Sequential (DOFS).
        run_test_case(
            build_cholesky_sequential_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "cholesky_sequential_inner_dofs",
            True,
            loop_node_index=2,
        )
        # Justification: This test case checks the outer loop (i loop) of the Cholesky sequential graph.
        # Expectation: The outer loop exhibits loop-carried dependencies. For example,
        # `L[i,j]` depends on `L[j-1, j-1]`, where `j-1` can refer to a value computed in a *previous*
        # iteration of the outer loop (`i' = j-1`). This cross-iteration dependency for the outer loop
        # forces sequential execution.
        # Therefore, it must be Data-Oblivious Full Sequential (DOFS).
        run_test_case(
            build_cholesky_sequential_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "cholesky_sequential_outer_dofs",
            True,
            loop_node_index=1,
        )

    def test_full_kernel_dofs(self):
        """
        More accurate Cholesky Decomposition kernel (fully sequential)
        for i = 0 to N-1:
          for j = 0 to i:
            sum_val = 0
            for k = 0 to j-1:
              sum_val = sum_val + L[i,k] * L[j,k]
            // L[i,j] = (A[i,j] - sum_val) / L[j,j]
            // (Simplified to L[i,j] = A[i,j] - sum_val for P3G modeling)

        This test expects the full Cholesky kernel to be Data-Oblivious Full Sequential (DOFS),
        meaning there exists a data configuration that forces sequential execution.
        """
        # Justification: The Cholesky kernel is known to be sequential due to multiple
        # loop-carried dependencies. Therefore, it is expected to be DOFS.
        run_test_case(
            build_cholesky_full_kernel_graph,
            exists_data_exists_bounds_forall_iter_isdep,
            "cholesky_full_kernel_dofs",
            True,
        )

    def test_sequential_dofs_forall_bounds(self):
        """
        Cholesky Decomposition-like kernel (fully sequential)
        for i = 2...N:
          for j = 2...i:
            L[i, j] = L[i, j-1] + L[j-1, j-1]

        This test expects both the inner and outer loops to be DOFS (Sequential)
        even when universally quantifying over loop bounds.
        """
        # Justification: The inner loop's dependency is independent of the specific loop bounds.
        run_test_case(
            build_cholesky_sequential_graph,
            exists_data_forall_bounds_forall_iters_chained,
            "cholesky_sequential_inner_dofs_forall_bounds",
            True,
            loop_node_index=2,
        )
        # Justification: The outer loop's dependency should also hold regardless of the
        # specific values of the loop bounds N.
        run_test_case(
            build_cholesky_sequential_graph,
            exists_data_forall_bounds_forall_iters_chained,
            "cholesky_sequential_outer_dofs_forall_bounds",
            True,
            loop_node_index=1,
        )

    def test_full_kernel_dofs_forall_bounds(self):
        """
        More accurate Cholesky Decomposition kernel (fully sequential)
        This test expects the full Cholesky kernel to be Data-Oblivious Full Sequential (DOFS),
        even when universally quantifying over loop bounds.
        """
        # Justification: The sequential nature of the Cholesky kernel is fundamental and
        # should not change based on the values of the loop bounds.
        run_test_case(
            build_cholesky_full_kernel_graph,
            exists_data_forall_bounds_forall_iters_chained,
            "cholesky_full_kernel_dofs_forall_bounds",
            True,
        )

    def test_sequential_find_dependency(self):
        """
        Cholesky Decomposition-like kernel (fully sequential)
        for i = 2...N:
          for j = 2...i:
            L[i, j] = L[i, j-1] + L[j-1, j-1]
        This test uses the relaxed SMT query to find *any* dependency.
        """
        # Justification: The inner loop has a clear dependency, so the query should find it.
        run_test_case(
            build_cholesky_sequential_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "cholesky_sequential_inner_find_dependency",
            True,
            loop_node_index=2,
        )
        # Justification: The outer loop also has dependencies, so the relaxed query should find one.
        run_test_case(
            build_cholesky_sequential_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "chlesky_sequential_outer_find_dependency",
            True,
            loop_node_index=1,
        )

    def test_full_kernel_find_dependency(self):
        """
        More accurate Cholesky Decomposition kernel (fully sequential)
        This test uses the relaxed SMT query to find *any* dependency.
        """
        # Justification: The full kernel is sequential, so a dependency must exist.
        run_test_case(
            build_cholesky_full_kernel_graph,
            exists_data_exists_bounds_exists_iter_isdep,
            "cholesky_full_kernel_find_dependency",
            True,
        )
