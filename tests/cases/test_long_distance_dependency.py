from pysmt.shortcuts import INT, Int, Minus, GT, LE

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_long_distance_dependency():
    """
    Loop with long-distance dependency (parallel from DOFS perspective)
    for i = 2...N: A[i] = A[max(i-10, 0)] + B[i]
    """
    print("--- Running Test: Loop with long-distance dependency ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")

    loop_node = None
    with b.add_loop("L1", "k", Int(2), N,
                    reads=[(A_root, (Int(0), N)), (B_root, (Int(2), N))],
                    writes=[(A_root, (Int(2), N))]) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")

        idx = Minus(k, Int(10))

        with b.add_branch("B1",
                          reads=[(A_local, idx), (B_local, k)],
                          writes=[(A_local, k)]) as B1:
            # if k - 10 > 0
            P1 = GT(Minus(k, Int(10)), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1 = b.add_data("A", is_output=True)
                B_path1 = b.add_data("B")
                b.add_compute("T1_gt",
                              reads=[(A_path1, idx), (B_path1, k)],
                              writes=[(A_path1, k)]
                              )

        idx = Int(0)
        with b.add_branch("B2",
                          reads=[(A_local, idx), (B_local, k)],
                          writes=[(A_local, k)]) as B2:
            # else
            P2 = LE(Minus(k, Int(10)), Int(0))
            with B2.add_path(P2):
                # Data nodes local to this path's graph
                A_path2 = b.add_data("A", is_output=True)
                B_path2 = b.add_data("B")
                b.add_compute("T2_le",
                              reads=[(A_path2, idx), (B_path2, k)],
                              writes=[(A_path2, k)]
                              )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end)

    # EXPECT: sat (True) - No dependency between adjacent iterations.
    result = solve_smt_string(smt_query, "long_distance_dependency")
    assert not result
    print("\nVerdict: Not fully sequential (DOFS). All checks PASSED.")
