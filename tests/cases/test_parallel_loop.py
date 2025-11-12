from pysmt.shortcuts import Int, Minus

from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
)
from tests.cases.graph_definitions import build_parallel_loop_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


class TestProveExistsDataForallIterIsdep:
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
        print("\n--- Running Test: Parallel Loop (Expected: Not DOFS/Parallel) ---")
        b_root_graph, loop_node, N, A_root, B_root, C_root = build_parallel_loop_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        loop_end = Minus(N, Int(1))
        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (parallel_loop_dofs) ---")
        print(smt_query)
        print("-------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across all adjacent iterations, as each iteration is independent.
        result = solve_smt_string(smt_query, "parallel_loop_dofs")
        assert not result, (
            "Expected parallel loop to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print("\nVerdict: PASSED. Parallel Loop is Not DOFS (Parallel) as expected.")


class TestProveExistsDataForallLoopBoundsIterIsdep:
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
        print(
            "\n--- Running Test: Parallel Loop (Loop Bounds) (Expected: Not DOFS/Parallel) ---"
        )
        b_root_graph, loop_node, N, A_root, B_root, C_root = build_parallel_loop_graph()

        # Print constructed P3G
        print_p3g_structure(b_root_graph)

        loop_end = Minus(N, Int(1))
        print(f"Generating SMT query for N (symbolic).")
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
        print("\n--- Generated SMT Query (parallel_loop_dofs_forall_bounds) ---")
        print(smt_query)
        print("-------------------------------------------")

        # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
        # across all adjacent iterations, as each iteration is independent.
        result = solve_smt_string(smt_query, "parallel_loop_dofs_forall_bounds")
        assert not result, (
            "Expected parallel loop (loop bounds) to be Not DOFS (parallel) but SMT solver returned SAT."
        )
        print(
            "\nVerdict: PASSED. Parallel Loop (Loop Bounds) is Not DOFS (Parallel) as expected."
        )
