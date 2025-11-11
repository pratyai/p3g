from pysmt.shortcuts import Symbol, INT, Minus, Int

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_disprove_dofs
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_nested_loop():
    """
    Nested Loop (Outer Seq, Inner Par)
    for i = 1...N:
      for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]
    """
    print("--- Running Test: Nested Loop (Outer Seq, Inner Par) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    M = b.add_symbol("M", INT)
    A = b.add_data("A", is_output=True)  # 2D array is implicitly handled by subset logic
    B = b.add_data("B")

    i_sym = Symbol("i", INT)
    j_sym = Symbol("j", INT)

    loop_node = None
    L_inner_node = None

    # Outer Loop (Sequential: A[i, j] depends on A[i-1, j])
    with b.add_loop("L_outer", "i", Int(1), N) as L_outer:
        i_sym = L_outer.loop_var
        loop_node = L_outer  # The highest level loop node for the SMT check

        # Inner Loop (Parallel: no dependency across j)
        with b.add_loop("L_inner", "j", Int(1), M) as L_inner:
            j_sym = L_inner.loop_var
            L_inner_node = L_inner

            # The innermost computation (A[i, j] = A[i-1, j] + B[i, j])
            # Use Tuple for 2D indexing
            reads_A = (A, (Minus(i_sym, Int(1)), j_sym))
            reads_B = (B, (i_sym, j_sym))
            writes_A = (A, (i_sym, j_sym))

            b.add_compute("T_comp",
                          reads=[reads_A, reads_B],
                          writes=[writes_A]
                          )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end_outer = N
    loop_end_inner = M

    # --- 1. Check Inner Loop (Expected: Parallel/SAT) ---
    print("\n-- 1. Checking Inner Loop (L_inner) for Parallelism --")
    smt_query_inner = generate_smt_for_disprove_dofs(L_inner_node, loop_end_inner)

    # EXPECT: sat (True) - L_inner has no self-dependencies on j
    result_inner = solve_smt_string(smt_query_inner, "nested_loop_inner")
    assert result_inner
    print("\nInner Loop Verdict: Not fully sequential (DOFS).")

    # --- 2. Check Outer Loop (Expected: Sequential/UNSAT) ---
    print("\n-- 2. Checking Outer Loop (L_outer) for Parallelism --")
    smt_query_outer = generate_smt_for_disprove_dofs(loop_node, loop_end_outer)

    # EXPECT: unsat (False) - L_outer has dependency A[i] <- A[i-1]
    result_outer = solve_smt_string(smt_query_outer, "nested_loop_outer")
    assert not result_outer
    print("\nOuter Loop Verdict: Sequential (DOFS). All checks PASSED.")
