from pysmt.shortcuts import INT, Int, Minus, GT, LE

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_sequential_with_symbolic_max_index():
    """
    Test case for a Sequential Loop with max(i-w, 0) index, where w is a symbolic variable.
    for i = 2...N: A[i] = A[max(i-w, 0)] + B[i]
    Since 'w' is a symbolic variable, the SMT solver can choose a value for 'w' (e.g., w=1)
    that makes the loop sequential (A[i] = A[max(i-1, 0)] + B[i] becomes A[i] = A[i-1] + B[i] for i > 0).
    Therefore, there exists a data configuration (a value for 'w') that forces sequentiality.
    This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
    meaning the SMT query should return SAT, indicating DOFS (sequential).
    """
    print("\n--- Running Test: Sequential Loop with symbolic max(i-w, 0) index (Expected: DOFS/Sequential) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    w = b.add_symbol("w", INT)
    A = b.add_data("A", is_output=True)
    B = b.add_data("B")

    loop_node = None
    with b.add_loop("L1", "k", Int(2), N,
                    reads=[(A, (Int(0), N)), (B, (Int(2), N))],
                    writes=[(A, (Int(2), N))]) as L1:
        k = L1.loop_var
        loop_node = L1

        with b.add_branch("B1",
                          reads=[(A, Minus(k, w)), (A, Int(0)), (B, k)],
                          writes=[(A, k)]) as B1:
            # if k - w > 0
            P1 = GT(Minus(k, w), Int(0))
            with B1.add_path(P1):
                idx = Minus(k, w)
                b.add_compute("T1_gt",
                              reads=[(A, idx), (B, k)],
                              writes=[(A, k)]
                              )
            # else
            P2 = LE(Minus(k, w), Int(0))
            with B1.add_path(P2):
                idx = Int(0)
                b.add_compute("T2_le",
                              reads=[(A, idx), (B, k)],
                              writes=[(A, k)]
                              )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    print(f"Generating SMT query for N (symbolic) and w (symbolic).")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end, verbose=False)
    print("\n--- Generated SMT Query (sequential_with_symbolic_max_index) ---")
    print(smt_query)
    print("-----------------------------------------------------------------")

    # EXPECT: sat (True) - A data configuration (value for w) exists that forces
    # sequential execution across all adjacent iterations.
    result = solve_smt_string(smt_query, "sequential_with_symbolic_max_index_check")
    assert result, "Expected sequential loop with symbolic max index to be DOFS (sequential) but SMT solver returned UNSAT."
    print("\nVerdict: PASSED. Sequential Loop with symbolic max(i-w, 0) index is DOFS (Sequential) as expected.")
