from pysmt.shortcuts import Symbol, INT, Int, Minus

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_nested_loop_outer_dofs():
    """
    Test case for a Nested Loop where the OUTER loop is DOFS:
    for i = 1...N:
      for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]

    The outer loop (over 'i') has a true data dependency (A[i,j] depends on A[i-1,j]),
    making it Data-Oblivious Full Sequential (DOFS).
    The inner loop (over 'j') has no self-dependency, making it Not DOFS (parallelizable).
    """
    print(
        "\n--- Running Test: Nested Loop (Expected: Outer DOFS/Sequential, Inner Not DOFS/Parallel) ---"
    )
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    M = b.add_symbol("M", INT)
    # Declare the existence of the data containers at the root level
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")

    loop_node = None
    L_inner_node = None

    # Outer Loop (Sequential: A[i, j] depends on A[i-1, j])
    with b.add_loop(
        "L_outer",
        "i",
        Int(1),
        N,
        reads=[
            (A_root, (Int(1), N)),
            (B_root, (Int(1), N)),
        ],  # Outer loop accesses A[1..N, ...] and B[1..N, ...]
        writes=[(A_root, (Int(1), N))],
    ) as L_outer:  # Outer loop writes A[1..N, ...]
        i_sym = L_outer.loop_var
        loop_node = L_outer  # The highest level loop node for the SMT check

        # Get local references to the data containers for this scope
        A_local_outer = b.add_data("A", is_output=True)
        B_local_outer = b.add_data("B")

        # Inner Loop (Parallel: no dependency across j)
        with b.add_loop(
            "L_inner",
            "j",
            Int(1),
            M,
            reads=[
                (A_local_outer, (Int(1), M)),
                (B_local_outer, (Int(1), M)),
            ],  # Inner loop accesses A[..., 1..M] and B[..., 1..M]
            writes=[(A_local_outer, (Int(1), M))],
        ) as L_inner:  # Inner loop writes A[..., 1..M]
            j_sym = L_inner.loop_var
            L_inner_node = L_inner

            # Get local references to the data containers for this scope
            A_local_inner = b.add_data("A", is_output=True)
            B_local_inner = b.add_data("B")

            # The innermost computation (A[i, j] = A[i-1, j] + B[i, j])
            # Use Tuple for 2D indexing
            reads_A = (A_local_inner, (Minus(i_sym, Int(1)), j_sym))
            reads_B = (B_local_inner, (i_sym, j_sym))
            writes_A = (A_local_inner, (i_sym, j_sym))

            b.add_compute("T_comp", reads=[reads_A, reads_B], writes=[writes_A])

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end_outer = N
    loop_end_inner = M

    # --- 1. Check Inner Loop (L_inner) ---
    print(
        "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: Not DOFS/Parallel) --"
    )
    # The inner loop has no self-dependencies on 'j'.
    # This means it is Not DOFS (parallelizable).
    smt_query_inner = generate_smt_for_prove_exists_data_forall_iter_isdep(
        L_inner_node, verbose=False
    )
    print("\n--- Generated SMT Query (nested_loop_outer_dofs_inner) ---")
    print(smt_query_inner)
    print("-----------------------------------------------")

    # EXPECT: unsat (False) - Inner loop has no self-dependencies on j
    result_inner = solve_smt_string(
        smt_query_inner, "nested_loop_outer_dofs_inner_check"
    )
    assert not result_inner, (
        "Expected inner loop to be Not DOFS (parallel) but SMT solver returned SAT."
    )
    print("\nInner Loop Verdict: PASSED. Not fully sequential (DOFS) as expected.")

    # --- 2. Check Outer Loop (L_outer) ---
    print(
        "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: DOFS/Sequential) --"
    )
    # The outer loop has a dependency A[i, j] <- A[i-1, j].
    # This means it is Data-Oblivious Full Sequential (DOFS).
    smt_query_outer = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, verbose=False
    )
    print("\n--- Generated SMT Query (nested_loop_outer_dofs_outer) ---")
    print(smt_query_outer)
    print("-----------------------------------------------")

    # EXPECT: sat (True) - Outer loop has dependency A[i] <- A[i-1]
    result_outer = solve_smt_string(
        smt_query_outer, "nested_loop_outer_dofs_outer_check"
    )
    assert result_outer, (
        "Expected outer loop to be DOFS (sequential) but SMT solver returned UNSAT."
    )
    print(
        "\nOuter Loop Verdict: PASSED. Sequential (DOFS) as expected. All checks PASSED."
    )


def test_nested_loop_inner_dofs():
    """
    Test case for a Nested Loop with inner loop DOFS:
    for i = 1...N:
      for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]

    The outer loop (over 'i') has no self-dependency, making it Not DOFS (parallelizable).
    The inner loop (over 'j') has a true data dependency (A[i,j] depends on A[i,j-1]),
    making it Data-Oblivious Full Sequential (DOFS).
    """
    print(
        "\n--- Running Test: Nested Loop (Expected: Outer Not DOFS/Parallel, Inner DOFS/Sequential) ---"
    )
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    M = b.add_symbol("M", INT)
    # Declare the existence of the data containers at the root level
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")

    loop_node = None
    L_inner_node = None

    # Outer Loop (Parallel: no dependency across i)
    with b.add_loop(
        "L_outer",
        "i",
        Int(1),
        N,
        reads=[
            (A_root, (Int(1), N)),
            (B_root, (Int(1), N)),
        ],  # Outer loop accesses A[1..N, ...] and B[1..N, ...]
        writes=[(A_root, (Int(1), N))],
    ) as L_outer:
        i_sym = L_outer.loop_var
        loop_node = L_outer  # The highest level loop node for the SMT check

        # Get local references to the data containers for this scope
        A_local_outer = b.add_data("A", is_output=True)
        B_local_outer = b.add_data("B")

        # Inner Loop (Sequential: A[i, j] depends on A[i, j-1])
        with b.add_loop(
            "L_inner",
            "j",
            Int(1),
            M,
            reads=[
                (A_local_outer, (Int(1), M)),
                (B_local_outer, (Int(1), M)),
            ],  # Inner loop accesses A[..., 1..M] and B[..., 1..M]
            writes=[(A_local_outer, (Int(1), M))],
        ) as L_inner:
            j_sym = L_inner.loop_var
            L_inner_node = L_inner

            # Get local references to the data containers for this scope
            A_local_inner = b.add_data("A", is_output=True)
            B_local_inner = b.add_data("B")

            # The innermost computation (A[i, j] = A[i, j-1] + B[i, j])
            # Use Tuple for 2D indexing
            reads_A = (
                A_local_inner,
                (i_sym, Minus(j_sym, Int(1))),
            )  # Dependency on j-1
            reads_B = (B_local_inner, (i_sym, j_sym))
            writes_A = (A_local_inner, (i_sym, j_sym))

            b.add_compute("T_comp", reads=[reads_A, reads_B], writes=[writes_A])

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end_outer = N
    loop_end_inner = M

    # --- 1. Check Inner Loop (L_inner) ---
    print(
        "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: DOFS/Sequential) --"
    )
    # The inner loop has a dependency A[i, j] <- A[i, j-1].
    # This means it is Data-Oblivious Full Sequential (DOFS).
    smt_query_inner = generate_smt_for_prove_exists_data_forall_iter_isdep(
        L_inner_node, verbose=False
    )
    print("\n--- Generated SMT Query (nested_loop_inner_dofs) ---")
    print(smt_query_inner)
    print("-----------------------------------------------")

    # EXPECT: sat (True) - Inner loop has dependency A[j] <- A[j-1]
    result_inner = solve_smt_string(smt_query_inner, "nested_loop_inner_dofs_check")
    assert result_inner, (
        "Expected inner loop to be DOFS (sequential) but SMT solver returned UNSAT."
    )
    print("\nInner Loop Verdict: PASSED. Sequential (DOFS) as expected.")

    # --- 2. Check Outer Loop (L_outer) ---
    print(
        "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: Not DOFS/Parallel) --"
    )
    # The outer loop has no self-dependencies on 'i'.
    # This means it is Not DOFS (parallelizable).
    smt_query_outer = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, verbose=False
    )
    print("\n--- Generated SMT Query (nested_loop_outer_not_dofs) ---")
    print(smt_query_outer)
    print("-----------------------------------------------")

    # EXPECT: unsat (False) - Outer loop has no self-dependencies on i
    result_outer = solve_smt_string(smt_query_outer, "nested_loop_outer_not_dofs_check")
    assert not result_outer, (
        "Expected outer loop to be Not DOFS (parallel) but SMT solver returned SAT."
    )
    print(
        "\nOuter Loop Verdict: PASSED. Not fully sequential (DOFS) as expected. All checks PASSED."
    )
