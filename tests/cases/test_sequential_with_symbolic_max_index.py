from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
)
from tests.cases.case_runner import run_test_case
from tests.cases.graph_definitions import (
    build_sequential_with_symbolic_max_index_graph,
)


class TestSequentialWithSymbolicMaxIndex:
    def test_sequential_with_symbolic_max_index_dofs(self):
        """
        Test case for a Sequential Loop with max(i-w, 0) index, where w is a symbolic variable.
        for i = 2...N: A[i] = A[max(i-w, 0)] + B[i]
        Since 'w' is a symbolic variable, the SMT solver can choose a value for 'w' (e.g., w=1)
        that makes the loop sequential (A[i] = A[max(i-1, 0)] + B[i] becomes A[i] = A[i-1] + B[i] for i > 0).
        Therefore, there exists a data configuration (a value for 'w') that forces sequentiality.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT, indicating DOFS (sequential).
        """
        run_test_case(
            build_sequential_with_symbolic_max_index_graph,
            generate_smt_for_prove_exists_data_forall_iter_isdep,
            "sequential_with_symbolic_max_index_dofs",
            True,
        )

    def test_sequential_with_symbolic_max_index_dofs_forall_bounds(self):
        """
        Test case for a Sequential Loop with max(i-w, 0) index, where w is a symbolic variable.
        for i = 2...N: A[i] = A[max(i-w, 0)] + B[i]
        Since 'w' is a symbolic variable, the SMT solver can choose a value for 'w' (e.g., w=1)
        that makes the loop sequential (A[i] = A[max(i-1, 0)] + B[i] becomes A[i] = A[i-1] + B[i] for i > 0).
        Therefore, there exists a data configuration (a value for 'w') that forces sequentiality.
        This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
        meaning the SMT query should return SAT, indicating DOFS (sequential).
        """
        run_test_case(
            build_sequential_with_symbolic_max_index_graph,
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
            "sequential_with_symbolic_max_index_dofs_forall_bounds",
            True,
        )

    def test_sequential_with_symbolic_max_index_find_dependency(self):
        """
        Test case for a Sequential Loop with max(i-w, 0) index, where w is a symbolic variable.
        for i = 2...N: A[i] = A[max(i-w, 0)] + B[i]
        This test uses the relaxed SMT query to find *any* dependency.
        A dependency exists if we can find a data configuration for w such that
        the loop has a dependency. For example, if w=1, the loop is sequential.
        The SMT query should return SAT.
        """
        run_test_case(
            build_sequential_with_symbolic_max_index_graph,
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
            "sequential_with_symbolic_max_index_find_dependency",
            True,
        )
