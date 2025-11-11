from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.shortcuts import INT, LE, Times, GT, Minus, Int

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_disprove_dofs
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_non_linear_predicate():
    """
    Non-linear Predicate
    for i=0:N {
      if i*i <= N: A[i] = B[i] + C[i]
      else: A[i] = A[i-1] + C[i]
    }
    """
    print("--- Running Test: Non-linear Predicate ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A = b.add_data("A", is_output=True)
    B = b.add_data("B")
    C = b.add_data("C")

    loop_node = None
    with b.add_loop("L1", "k", Int(0), N) as L1:
        k = L1.loop_var
        loop_node = L1

        with b.add_branch("B1") as B1:
            P1 = LE(Times(k, k), N)
            with B1.add_path(P1):
                b.add_compute("T1_par",
                              reads=[(B, k), (C, k)],
                              writes=[(A, k)]
                              )

            P2 = GT(Times(k, k), N)
            with B1.add_path(P2):
                b.add_compute("T2_seq",
                              reads=[(A, Minus(k, Int(1))), (C, k)],
                              writes=[(A, k)]
                              )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_disprove_dofs(loop_node, loop_end)

    # EXPECT: sat (True) - Universal counterexample (e.g., N=100, k=2) exists
    result = False
    try:
        result = solve_smt_string(smt_query, "non_linear_predicate")
    except SolverReturnedUnknownResultError:
        # Conservatively assume sequential for the undecidable case
        print(
            "NOTE: Solver returned 'unknown' for Case 6. Cannot prove parallelism. Conservatively assuming sequential (False).")
        result = False

    assert result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")
