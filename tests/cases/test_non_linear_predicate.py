from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.shortcuts import INT, LE, Times, GT, Minus, Int

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
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
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")
    C_root = b.add_data("C")

    loop_node = None
    with b.add_loop("L1", "k", Int(0), N,
                    reads=[(A_root, (Int(0), Minus(N, Int(1)))), (B_root, (Int(0), N)), (C_root, (Int(0), N))],
                    writes=[(A_root, (Int(0), N))]) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        C_local = b.add_data("C")

        with b.add_branch("B1",
                          reads=[(A_local, Minus(k, Int(1))), (A_local, k), (B_local,k), (C_local, k)],
                          writes=[(A_local, k)]) as B1:
            P1 = LE(Times(k, k), N)
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1 = b.add_data("A", is_output=True)
                B_path1 = b.add_data("B")
                C_path1 = b.add_data("C")
                b.add_compute("T1_par",
                              reads=[(B_path1, k), (C_path1, k)],
                              writes=[(A_path1, k)]
                              )

            P2 = GT(Times(k, k), N)
            with B1.add_path(P2):
                # Data nodes local to this path's graph
                A_path2 = b.add_data("A", is_output=True)
                B_path2 = b.add_data("B")
                C_path2 = b.add_data("C")
                b.add_compute("T2_seq",
                              reads=[(A_path2, Minus(k, Int(1))), (C_path2, k)],
                              writes=[(A_path2, k)]
                              )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end)

    # EXPECT: sat (True) - Universal counterexample (e.g., N=100, k=2) exists
    result = solve_smt_string(smt_query, "non_linear_predicate")
    assert result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")
