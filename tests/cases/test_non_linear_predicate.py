from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.cases.graph_definitions import build_non_linear_predicate_graph
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_non_linear_predicate():
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
    print("\n--- Running Test: Non-linear Predicate (Expected: DOFS/Sequential) ---")
    b_root_graph, loop_node, N, A_root, B_root, C_root = build_non_linear_predicate_graph()

    # Print constructed P3G
    print_p3g_structure(b_root_graph)

    print(f"Generating SMT query for N (symbolic).")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, verbose=False
    )
    print("\n--- Generated SMT Query (non_linear_predicate) ---")
    print(smt_query)
    print("--------------------------------------------------")

    # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
    # across all adjacent iterations, as the parallel branch can always be taken.
    result = solve_smt_string(smt_query, "non_linear_predicate_check")
    assert not result, (
        "Expected non-linear predicate loop to be Not DOFS (parallel) but SMT solver returned SAT."
    )
    print(
        "\nVerdict: PASSED. Non-linear Predicate loop is Not DOFS (Parallel) as expected."
    )
