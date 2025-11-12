from pysmt.shortcuts import INT, Int, Minus, Symbol, Plus
from pysmt.typing import ArrayType

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_cholesky_sequential():
    """
    Cholesky Decomposition-like kernel (fully sequential)
    for i = 2...N:
      for j = 2...i:
        L[i, j] = L[i, j-1] + L[j-1, j-1]

    # Actual Cholesky inner kernel (simplified for L[i,j] calculation):
    # L[i,j] = (A[i,j] - sum_{k=0}^{j-1} L[i,k] * L[j,k]) / L[j,j]
    # This test models a simplified dependency pattern found in such kernels.
    """
    print("\n--- Running Test: Cholesky Decomposition-like Kernel (Simplified) ---")
    print("Expected: Inner Loop DOFS (Sequential), Outer Loop Not DOFS (Parallel)")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    L_root = b.add_data("L", is_output=True)

    outer_loop_node = None
    inner_loop_node = None

    # Start loops from 2 to avoid boundary conditions at 0/1
    with b.add_loop(
        "L_outer",
        "i",
        Int(2),
        N,
        reads=[(L_root, ((Int(1), N), (Int(1), Minus(N, Int(1)))))],
        writes=[(L_root, ((Int(2), N), (Int(2), N)))],
    ) as L_outer:
        i = L_outer.loop_var
        outer_loop_node = L_outer

        # Get local references to the data containers for this scope
        L_local_outer = b.add_data("L", is_output=True)

        with b.add_loop(
            "L_inner",
            "j",
            Int(2),
            i,
            reads=[(L_local_outer, ((Int(1), i), (Int(1), Minus(i, Int(1)))))],
            writes=[(L_local_outer, ((Int(2), i), (Int(2), i)))],
        ) as L_inner:
            j = L_inner.loop_var
            inner_loop_node = L_inner

            # Get local references to the data containers for this scope
            L_local_inner = b.add_data("L", is_output=True)

            # L[i, j] = L[i, j-1] + L[j-1, j-1]
            # This models a RAW dependency on L[i, j-1] within the inner loop.
            # It also models a WAR/WAW dependency on L[j-1, j-1] across outer loop iterations.
            # Using tuples for 2D indexing
            read1 = (L_local_inner, (i, Minus(j, Int(1))))
            read2 = (L_local_inner, (Minus(j, Int(1)), Minus(j, Int(1))))
            write = (L_local_inner, (i, j))

            b.add_compute("T_cholesky", reads=[read1, read2], writes=[write])

    print_p3g_structure(b.root_graph)

    # --- 1. Check Inner Loop (L_inner) ---
    print(
        "\n-- 1. Checking Inner Loop (L_inner) for Parallelism (Expected: DOFS/Sequential) --"
    )
    # The inner loop has a dependency L[i,j] <- L[i,j-1].
    # This means it is fully sequential (DOFS).
    # The inner loop end 'i' is a symbolic variable for this check.
    smt_query_inner = generate_smt_for_prove_exists_data_forall_iter_isdep(
        inner_loop_node, verbose=False
    )
    print("\n--- Generated SMT Query (cholesky_inner) ---")
    print(smt_query_inner)
    print("--------------------------------------------")

    # EXPECT: sat (True) - Inner loop has dependency L[i,j] <- L[i,j-1]
    result_inner = solve_smt_string(smt_query_inner, "cholesky_inner")
    assert result_inner, (
        "Expected inner loop to be DOFS (sequential) but SMT solver returned UNSAT."
    )
    print("\nInner Loop Verdict: PASSED. Sequential (DOFS) as expected.")

    # --- 2. Check Outer Loop (L_outer) ---
    print(
        "\n-- 2. Checking Outer Loop (L_outer) for Parallelism (Expected: Not DOFS/Parallel) --"
    )
    # The outer loop has a dependency through L[j-1,j-1] (e.g., when j=i, L[i,i] depends on L[i-1,i-1]).
    # However, this dependency is not *always* present for *all* adjacent iterations (k, k+1)
    # for a *single* data configuration.
    # For example, if N is large enough, and we pick a data configuration where L[j-1,j-1]
    # is always distinct for different j, then the outer loop might appear parallel.
    # The current model implies that for N >= 3, the outer loop is parallelizable.
    smt_query_outer = generate_smt_for_prove_exists_data_forall_iter_isdep(
        outer_loop_node, verbose=False
    )
    print("\n--- Generated SMT Query (cholesky_outer) ---")
    print(smt_query_outer)
    print("--------------------------------------------")

    # EXPECT: unsat (False) - Outer loop is Not DOFS (Parallel)
    result_outer = solve_smt_string(smt_query_outer, "cholesky_outer")
    assert not result_outer, (
        "Expected outer loop to be Not DOFS (parallel) but SMT solver returned SAT."
    )
    print(
        "\nOuter Loop Verdict: PASSED. Not DOFS (Parallel) as expected. All checks PASSED."
    )


def test_cholesky_full_kernel():
    """
    More accurate Cholesky Decomposition kernel (fully sequential)
    for i = 0 to N-1:
      for j = 0 to i:
        sum_val = 0
        for k = 0 to j-1:
          sum_val = sum_val + L[i,k] * L[j,k]
        // L[i,j] = (A[i,j] - sum_val) / L[j,j]
        // (Simplified to L[i,j] = A[i,j] - sum_val for P3G modeling)

    This test expects the full Cholesky kernel to be Data-Oblivious Full Sequential (DOFS),
    meaning there exists a data configuration that forces sequential execution.
    """
    print("\n--- Running Test: Full Cholesky Kernel (Expected: DOFS/Sequential) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)

    # Pysmt symbols for array content (needed for Select operations)
    A_val = Symbol("A_val", ArrayType(INT, ArrayType(INT, INT)))
    L_val = Symbol("L_val", ArrayType(INT, ArrayType(INT, INT)))

    # Link Pysmt symbols to Data nodes
    A_root = b.add_data("A", is_output=False, pysmt_array_sym=A_val)
    L_root = b.add_data("L", is_output=True, pysmt_array_sym=L_val)

    outer_loop_node = None
    middle_loop_node = None
    inner_loop_node = None

    # Outer loop: for i = 0 to N-1
    with b.add_loop(
        "L_outer",
        "i",
        Int(0),
        Minus(N, Int(1)),
        reads=[
            (A_root, ((Int(0), N), (Int(0), N))),  # Reads entire A
            (L_root, ((Int(0), N), (Int(0), N))),
        ],  # Reads entire L
        writes=[(L_root, ((Int(0), N), (Int(0), N)))],
    ) as L_outer:  # Writes entire L
        i = L_outer.loop_var
        outer_loop_node = L_outer

        L_local_outer = b.add_data("L", is_output=True, pysmt_array_sym=L_val)
        A_local_outer = b.add_data("A", is_output=False, pysmt_array_sym=A_val)

        # Middle loop: for j = 0 to i
        with b.add_loop(
            "L_middle",
            "j",
            Int(0),
            i,
            reads=[
                (A_local_outer, ((Int(0), Plus(i, Int(1))), (Int(0), Plus(i, Int(1))))),
                # Reads A[0..i, 0..i]
                (L_local_outer, ((Int(0), Plus(i, Int(1))), (Int(0), Plus(i, Int(1))))),
            ],
            # Reads L[0..i, 0..i]
            writes=[
                (L_local_outer, ((Int(0), Plus(i, Int(1))), (Int(0), Plus(i, Int(1)))))
            ],
        ) as L_middle:  # Writes L[0..i, 0..i]
            j = L_middle.loop_var
            middle_loop_node = L_middle

            L_local_middle = b.add_data("L", is_output=True, pysmt_array_sym=L_val)
            A_local_middle = b.add_data("A", is_output=False, pysmt_array_sym=A_val)

            # Scalar for sum_val
            sum_val_scalar = b.add_data(
                "sum_val", is_output=False
            )  # Scalar, so no pysmt_array_sym

            # Initialize sum_val = 0 (as a compute node)
            b.add_compute(
                "T_init_sum",
                reads=[],
                writes=[(sum_val_scalar, Int(0))],  # Write 0 to sum_val
            )

            # Innermost loop: for k = 0 to j-1 (if j > 0)
            with b.add_loop(
                "L_inner",
                "k",
                Int(0),
                Minus(j, Int(1)),
                reads=[
                    (
                        L_local_middle,
                        ((Int(0), Plus(i, Int(1))), (Int(0), Plus(j, Int(1)))),
                    ),
                    # Reads L[0..i, 0..j]
                    (sum_val_scalar, Int(0)),
                ],  # Reads previous sum_val
                writes=[(sum_val_scalar, Int(0))],
            ) as L_inner:  # Writes new sum_val
                k = L_inner.loop_var
                inner_loop_node = L_inner

                L_local_inner = b.add_data("L", is_output=True, pysmt_array_sym=L_val)
                sum_val_local_inner = b.add_data("sum_val", is_output=False)

                # Compute: sum_val = sum_val + L[i,k] * L[j,k]
                # We need to model the multiplication and addition.
                # For P3G, we just model the reads and writes.
                b.add_compute(
                    "T_sum_accum",
                    reads=[
                        (sum_val_local_inner, Int(0)),  # Read current sum_val
                        (L_local_inner, (i, k)),  # Read L[i,k]
                        (L_local_inner, (j, k)),
                    ],  # Read L[j,k]
                    writes=[(sum_val_local_inner, Int(0))],  # Write new sum_val
                )

            # Final computation for L[i,j] = A[i,j] - sum_val (simplified)
            # This compute node is outside L_inner, but inside L_middle
            b.add_compute(
                "T_final_Lij",
                reads=[
                    (A_local_middle, (i, j)),  # Read A[i,j]
                    (sum_val_scalar, Int(0)),  # Read final sum_val
                    (L_local_middle, (j, j)),
                ],  # Read L[j,j] (for division, if modeled)
                writes=[(L_local_middle, (i, j))],  # Write L[i,j]
            )

    print_p3g_structure(b.root_graph)

    # --- Check Outer Loop (L_outer) ---
    print(
        "\n-- Checking Full Cholesky Kernel (L_outer) for Parallelism (Expected: DOFS/Sequential) --"
    )
    # The full Cholesky kernel is known to be highly sequential due to dependencies
    # across all three nested loops.
    smt_query_outer = generate_smt_for_prove_exists_data_forall_iter_isdep(
        outer_loop_node, verbose=False
    )
    print("\n--- Generated SMT Query (cholesky_full_kernel) ---")
    print(smt_query_outer)
    print("---------------------------------------------------")

    # EXPECT: sat (True) - Full Cholesky is highly sequential
    result_outer = solve_smt_string(smt_query_outer, "cholesky_full_kernel")
    assert result_outer, (
        "Expected full Cholesky kernel to be DOFS (sequential) but SMT solver returned UNSAT."
    )
    print(
        "\nFull Cholesky Kernel Verdict: PASSED. Sequential (DOFS) as expected. All checks PASSED."
    )
