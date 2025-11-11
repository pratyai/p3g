from pysmt.shortcuts import Symbol, INT, LE, GT, Int, ArrayType, Select, Minus

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_data_aware_bi():
    """
    Data-Aware (B[i])
    for i = 1...N: if (B[i] > 0) then A[i] = A[i-1]
    """
    print("--- Running Test: Data-Aware (B[i]) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")
    B_val = Symbol("B_val", ArrayType(INT, INT))

    loop_node = None
    with b.add_loop("L1", "k", Int(1), N,
                    reads=[(A_root, (Int(0), Minus(N, Int(1)))), (B_root, (Int(1), N))],
                    writes=[(A_root, (Int(1), N))]) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")

        with b.add_branch("B1",
                          reads=[(A_local, Minus(k, Int(1))), (B_local, k)],
                          writes=[(A_local, k)]) as B1:
            P1 = GT(Select(B_val, k), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1 = b.add_data("A", is_output=True)
                B_path1 = b.add_data("B")
                b.add_compute("T1_seq",
                              reads=[(B_path1, k), (A_path1, Minus(k, Int(1)))],
                              writes=[(A_path1, k)]
                              )

        with b.add_branch("B2",
                          reads=[(B_local, k)],
                          writes=[]) as B2:
            P2 = LE(Select(B_val, k), Int(0))
            with B2.add_path(P2):
                # Data nodes local to this path's graph
                B_path2 = b.add_data("B")
                b.add_compute("T2_skip",
                              reads=[(B_path2, k)],
                              writes=[]
                              )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end)

    # EXPECT: unsat (False) - No universal counterexample exists
    result = solve_smt_string(smt_query, "data_aware_bi")
    assert result
    print("\nVerdict: Sequential (DOFS). All checks PASSED.")
