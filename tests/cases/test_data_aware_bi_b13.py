from pysmt.shortcuts import Symbol, INT, ArrayType, Int, Select, GT, Minus, LE, GE

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_data_aware_bi_b13():
    """
    Data-Aware (B[i] - B[13])
    for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1]
    """
    print("--- Running Test: Data-Aware (B[i] - B[13]) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    B_val = Symbol("B_val", ArrayType(INT, INT))
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B", pysmt_array_sym=B_val)

    const_idx = Int(13)

    loop_node = None
    with b.add_loop("L1", "k", Int(1), N,
                    reads=[(A_root, (Int(0), Minus(N, Int(1)))), (B_root, (Int(1), N)), (B_root, const_idx)],
                    writes=[(A_root, (Int(1), N))]) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")

        with b.add_branch("B1",
                          reads=[(A_local, Minus(k, Int(1))), (A_local, k), (B_local, k), (B_local, const_idx)],
                          writes=[(A_local, k)]) as B1:
            val_k = Select(B_val, k)
            val_13 = Select(B_val, const_idx)

            P1 = GT(Minus(val_k, val_13), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1 = b.add_data("A", is_output=True)
                B_path1 = b.add_data("B")
                b.add_compute("T1_seq",
                              reads=[(B_path1, k), (B_path1, const_idx), (A_path1, Minus(k, Int(1))), (A_path1, k)],
                              writes=[(A_path1, k)]
                              )
        # with b.add_branch("B2",
        #                   reads=[(B_local, k), (B_local, const_idx)],
        #                   writes=[]) as B2:
        #     val_k = Select(B_val, k)
        #     val_13 = Select(B_val, const_idx)
        #
        #     P2 = LE(Minus(val_k, val_13), Int(0))
        #     with B2.add_path(P2):
        #         # Data nodes local to this path's graph
        #         A_path2 = b.add_data("A", is_output=True)
        #         B_path2 = b.add_data("B")
        #         b.add_compute("T2_skip",
        #                       reads=[(B_path2, k), (B_path2, const_idx)],
        #                       writes=[])

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end)

    # EXPECT: sat (True) - Universal counterexample (k=12, N=13) exists
    result = solve_smt_string(smt_query, "data_aware_bi_b13")
    assert result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")


def test_data_aware_bi_b13_high_N():
    """
    Data-Aware (B[i] - B[13])
    for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1]
    """
    print("--- Running Test: Data-Aware (B[i] - B[13]) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_val = Symbol("B_val", ArrayType(INT, INT))
    B_root = b.add_data("B", pysmt_array_sym=B_val)

    const_idx = Int(13)

    loop_node = None
    with b.add_loop("L1", "k", Int(1), N,
                    reads=[(A_root, (Int(0), Minus(N, Int(1)))), (B_root, (Int(1), N)), (B_root, const_idx)],
                    writes=[(A_root, (Int(1), N))]) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")

        with b.add_branch("B1",
                          reads=[(A_local, Minus(k, Int(1))), (B_local, k), (B_local, const_idx)],
                          writes=[(A_local, k)]) as B1:
            val_k = Select(B_val, k)
            val_13 = Select(B_val, const_idx)

            P1 = GT(Minus(val_k, val_13), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1 = b.add_data("A", is_output=True)
                B_path1 = b.add_data("B")
                b.add_compute("T1_seq",
                              reads=[(B_path1, k), (B_path1, const_idx), (A_path1, Minus(k, Int(1)))],
                              writes=[(A_path1, k)]
                              )

        # with b.add_branch("B2",
        #                   reads=[(B_local, k), (B_local, const_idx)],
        #                   writes=[]) as B2:
        #     val_k = Select(B_val, k)
        #     val_13 = Select(B_val, const_idx)
        #
        #     P2 = LE(Minus(val_k, val_13), Int(0))
        #     with B2.add_path(P2):
        #         # Data nodes local to this path's graph
        #         B_path2 = b.add_data("B")
        #         b.add_compute("T2_skip",
        #                       reads=[(B_path2, k), (B_path2, const_idx)],
        #                       writes=[])

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, loop_end, extra_assertions=[GE(N, Int(15))])

    # EXPECT: sat (True) - Universal counterexample (k=12, N=13) exists
    result = solve_smt_string(smt_query, "data_aware_bi_b13")
    assert not result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")
