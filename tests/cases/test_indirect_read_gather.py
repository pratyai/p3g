from pysmt.shortcuts import Symbol, INT, ArrayType, Int, Select

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep
from tests.test_utils import print_p3g_structure, solve_smt_string


def test_indirect_read_gather():
    """
    Test case for Indirect Read (Gather) operation: for i = 1...N: A[i] = B[ IDX[i] ].
    This operation is generally parallelizable because writes to A[i] are independent
    of previous A values, and reads from B are indirect.
    There is no inherent data dependency between adjacent iterations that would force
    sequential execution for all data configurations.
    This test expects the loop to be Not Data-Oblivious Full Sequential (Not DOFS),
    meaning it is parallelizable.
    The SMT query should return UNSAT, indicating Not DOFS (parallel).
    """
    print(
        "\n--- Running Test: Indirect Read (Gather) (Expected: Not DOFS/Parallel) ---"
    )
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")
    IDX_val = Symbol("IDX_val", ArrayType(INT, INT))
    IDX_root = b.add_data("IDX", pysmt_array_sym=IDX_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[(B_root, (Int(0), N)), (IDX_root, (Int(0), N))],
        writes=[(A_root, (Int(0), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        IDX_local = b.add_data("IDX")

        read_idx = Select(IDX_val, k)

        b.add_compute(
            "T1_gather",
            reads=[(B_local, read_idx), (IDX_local, k)],
            writes=[(A_local, k)],
        )

    # Print constructed P3G
    print_p3g_structure(b.root_graph)

    loop_end = N
    print(f"Generating SMT query for N (symbolic).")
    smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node, verbose=False
    )
    print("\n--- Generated SMT Query (indirect_read_gather) ---")
    print(smt_query)
    print("--------------------------------------------------")

    # EXPECT: unsat (False) - No data configuration exists that forces sequentiality
    # across all adjacent iterations.
    result = solve_smt_string(smt_query, "indirect_read_gather_check")
    assert not result, (
        "Expected indirect read (gather) to be Not DOFS (parallel) but SMT solver returned SAT."
    )
    print(
        "\nVerdict: PASSED. Indirect Read (Gather) is Not DOFS (Parallel) as expected."
    )
