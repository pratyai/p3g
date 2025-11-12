from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.cases.graph_definitions import build_long_distance_dependency_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_long_distance_dependency():
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
    print(
        "\n--- Running Test: Loop with long-distance dependency (Expected: Not DOFS/Parallel) ---"
    )
    b_root_graph, loop_node, N, A_root, B_root = build_long_distance_dependency_graph()

    # Print constructed P3G
    print_p3g_structure(b_root_graph)

    print(f"Generating SMT query for N (symbolic).")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, verbose=False
    )
    print("\n--- Generated SMT Query (long_distance_dependency) ---")
    print(smt_query)
    print("----------------------------------------------------")

    # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
    # across all adjacent iterations due to the long-distance dependency.
    result = solve_smt_string(smt_query, "long_distance_dependency_check")
    assert not result, (
        "Expected long-distance dependency loop to be Not DOFS (parallel) but SMT solver returned SAT."
    )
    print(
        "\nVerdict: PASSED. Long-distance dependency loop is Not DOFS (Parallel) as expected."
    )
