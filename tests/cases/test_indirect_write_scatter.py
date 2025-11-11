from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.shortcuts import Symbol, INT, ArrayType, Int, Select

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_indirect_write_scatter():
    """
    Indirect Write (Scatter) - Sequential
    for i = 1...N: A[ IDX[i] ] = B[i]
    """
    print("--- Running Test: Indirect Write (Scatter) ---")
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")
    IDX_val = Symbol("IDX_val", ArrayType(INT, INT))
    IDX_root = b.add_data("IDX", pysmt_array_sym=IDX_val)

    loop_node = None
    with b.add_loop("L1", "k", Int(1), N,
                    reads=[(B_root, (Int(0), N)), (IDX_root, (Int(0), N))],
                    writes=[(A_root, (Int(0), N))]) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        IDX_local = b.add_data("IDX")

        write_idx = Select(IDX_val, k)

        b.add_compute("T1_scatter",
                      reads=[(B_local, k), (IDX_local, k)],
                      writes=[(A_local, write_idx)]
                      )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    # Drop extra_assertions by calling with default parameters
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop_node, loop_end)

    # EXPECT: unsat (False) - No universal counterexample exists
    result = solve_smt_string(smt_query, "indirect_write_scatter")
    assert not result
    print("\nVerdict: Sequential (DOFS). All checks PASSED.")
