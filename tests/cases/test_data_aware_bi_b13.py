from pysmt.shortcuts import Symbol, INT, ArrayType, Int, Select, GT, Minus, LE, GE

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_data_aware_bi_b13():
    """
    Test case for a Data-Aware loop: for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
    This test expects the loop to be Data-Oblivious Full Sequential (DOFS),
    meaning there exists a data configuration that forces sequential execution.
    For example, if B[i] = 1 for all i, and B[13] = 0, then B[i] - B[13] > 0 is always true,
    and the loop becomes A[i] = A[i-1], which is sequential.
    The SMT query should return SAT, indicating DOFS (sequential).
    """
    print(
        "\n--- Running Test: Data-Aware (B[i] - B[13]) (Expected: DOFS/Sequential) ---"
    )
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    B_val = Symbol("B_val", ArrayType(INT, INT))
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B", pysmt_array_sym=B_val)

    const_idx = Int(13)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[
            (A_root, (Int(0), Minus(N, Int(1)))),
            (B_root, (Int(1), N)),
            (B_root, const_idx),
        ],
        writes=[(A_root, (Int(1), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")

        with b.add_branch(
            "B1",
            reads=[
                (A_local, Minus(k, Int(1))),
                (A_local, k),
                (B_local, k),
                (B_local, const_idx),
            ],
            writes=[(A_local, k)],
        ) as B1:
            val_k = Select(B_val, k)
            val_13 = Select(B_val, const_idx)

            P1 = GT(Minus(val_k, val_13), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1 = b.add_data("A", is_output=True)
                B_path1 = b.add_data("B")
                b.add_compute(
                    "T1_seq",
                    reads=[
                        (B_path1, k),
                        (B_path1, const_idx),
                        (A_path1, Minus(k, Int(1))),
                        (A_path1, k),
                    ],
                    writes=[(A_path1, k)],
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
    print(f"Generating SMT query for N (symbolic) with no extra assertions.")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, verbose=False
    )
    print("\n--- Generated SMT Query (data_aware_bi_b13) ---")
    print(smt_query)
    print("-----------------------------------------------")

    # EXPECT: sat (True) - A data configuration exists that forces sequential execution.
    # The SMT solver will find a suitable N and values for B such that the condition
    # (B[i] - B[13] > 0) is always true for all relevant i, making the loop sequential.
    result = solve_smt_string(smt_query, "data_aware_bi_b13_check")
    assert result, (
        "Expected data-aware loop to be DOFS (sequential) but SMT solver returned UNSAT."
    )
    print("\nVerdict: PASSED. Data-aware loop is DOFS (Sequential) as expected.")


def test_data_aware_bi_b13_high_N():
    """
    Test case for a Data-Aware loop: for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
    This test adds an assertion N >= 15.
    When N >= 15, the loop includes k=13. For k=13, the condition B[13] - B[13] > 0 is false,
    meaning the assignment A[13] = A[12] is skipped.
    Since there's at least one iteration (k=13) where the dependency is not guaranteed,
    the loop is Not Data-Oblivious Full Sequential (Not DOFS), meaning it is parallelizable.
    The SMT query should return UNSAT, indicating Not DOFS (parallel).
    """
    print(
        "\n--- Running Test: Data-Aware (B[i] - B[13]) High N (Expected: Not DOFS/Parallel) ---"
    )
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_val = Symbol("B_val", ArrayType(INT, INT))
    B_root = b.add_data("B", pysmt_array_sym=B_val)

    const_idx = Int(13)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[
            (A_root, (Int(0), Minus(N, Int(1)))),
            (B_root, (Int(1), N)),
            (B_root, const_idx),
        ],
        writes=[(A_root, (Int(1), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")

        with b.add_branch(
            "B1",
            reads=[(A_local, Minus(k, Int(1))), (B_local, k), (B_local, const_idx)],
            writes=[(A_local, k)],
        ) as B1:
            val_k = Select(B_val, k)
            val_13 = Select(B_val, const_idx)

            P1 = GT(Minus(val_k, val_13), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1 = b.add_data("A", is_output=True)
                B_path1 = b.add_data("B")
                b.add_compute(
                    "T1_seq",
                    reads=[
                        (B_path1, k),
                        (B_path1, const_idx),
                        (A_path1, Minus(k, Int(1))),
                    ],
                    writes=[(A_path1, k)],
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
    print(f"Generating SMT query for N (symbolic) with extra assertion: N >= 15.")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, extra_assertions=[GE(N, Int(15))], verbose=False
    )
    print("\n--- Generated SMT Query (data_aware_bi_b13_high_N) ---")
    print(smt_query)
    print("-----------------------------------------------------")

    # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
    # across all adjacent iterations when N >= 15, because the dependency is skipped for k=13.
    result = solve_smt_string(smt_query, "data_aware_bi_b13_high_N_check")
    assert not result, (
        "Expected data-aware loop to be Not DOFS (parallel) but SMT solver returned SAT."
    )
    print(
        "\nVerdict: PASSED. Data-aware loop is Not DOFS (Parallel) as expected for N >= 15."
    )
