from pysmt.shortcuts import INT, Int, Minus

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_sequential_loop():
    """
    Test case for a Sequential Loop: for i = 2...N: A[i] = A[i-1] + B[i].
    This loop has a Read-After-Write (RAW) dependency: A[i] reads A[i-1],
    which was written in the previous iteration. This dependency exists for all
    iterations in the loop range.
    Therefore, the loop is inherently sequential.
    This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
    meaning the SMT query should return SAT, indicating DOFS (sequential).
    """
    print("\n--- Running Test: Sequential Loop (Expected: DOFS/Sequential) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")

    loop_node = None
    with b.add_loop("L1", "k", Int(2), N,
                    reads=[(A_root, (Int(1), Minus(N, Int(1)))), (B_root, (Int(2), N))],
                    writes=[(A_root, (Int(2), N))]) as L1:
        k = L1.loop_var
        loop_node = L1
        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        b.add_compute("T1",
                      reads=[(A_local, Minus(k, Int(1))), (B_local, k)],
                      writes=[(A_local, k)]
                      )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    print(f"Generating SMT query for N (symbolic).")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end, verbose=False)
    print("\n--- Generated SMT Query (sequential_loop) ---")
    print(smt_query)
    print("---------------------------------------------")

    # EXPECT: sat (True) - A data configuration exists that forces sequential execution
    # across all adjacent iterations due to the RAW dependency.
    result = solve_smt_string(smt_query, "sequential_loop_check")
    assert result, "Expected sequential loop to be DOFS (sequential) but SMT solver returned UNSAT."
    print("\nVerdict: PASSED. Sequential Loop is DOFS (Sequential) as expected.")
