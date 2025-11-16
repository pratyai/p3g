from pysmt.shortcuts import (
    Symbol,
    INT,
    Plus,
    Int,
    LE,
    ArrayType,
    Select,
    Minus,
    Times,
    Div,
    GT,
)

from p3g.p3g import GraphBuilder, PysmtRange, PysmtCoordSet


def build_array_reversal_graph():
    """
    Helper to create a P3G graph for Array Reversal.
    Represents a program like: for i = 0...N-1: swap(A[i], A[N-1-i]).
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(0),
        Minus(N, Int(1)),
        reads=[(A_root, PysmtRange(Int(0), Minus(N, Int(1))))],
        writes=[(A_root, PysmtRange(Int(0), Minus(N, Int(1))))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        idx_rev = Minus(Minus(N, Int(1)), k)

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)

        b.add_compute(
            "T1_swap",
            reads=[(A_local, k), (A_local, idx_rev)],
            writes=[(A_local, k), (A_local, idx_rev)],
        )
    return b.root_graph, loop_node, N, A_root


def build_cholesky_sequential_graph():
    """
    Helper to create a P3G graph for a Cholesky Decomposition-like kernel.
    for i = 2...N:
      for j = 2...i:
        L[i, j] = L[i, j-1] + L[j-1, j-1]
    """
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
        reads=[
            (
                L_root,
                PysmtCoordSet(
                    PysmtRange(Int(1), N), PysmtRange(Int(1), Minus(N, Int(1)))
                ),
            )
        ],
        writes=[(L_root, PysmtCoordSet(PysmtRange(Int(2), N), PysmtRange(Int(2), N)))],
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
            reads=[
                (
                    L_local_outer,
                    PysmtCoordSet(
                        PysmtRange(Int(1), i), PysmtRange(Int(1), Minus(i, Int(1)))
                    ),
                )
            ],
            writes=[
                (
                    L_local_outer,
                    PysmtCoordSet(PysmtRange(Int(2), i), PysmtRange(Int(2), i)),
                )
            ],
        ) as L_inner:
            j = L_inner.loop_var
            inner_loop_node = L_inner

            # Get local references to the data containers for this scope
            L_local_inner = b.add_data("L", is_output=True)

            # L[i, j] = L[i, j-1] + L[j-1, j-1]
            # This models a RAW dependency on L[i, j-1] within the inner loop.
            # It also models a WAR/WAW dependency on L[j-1, j-1] across outer loop iterations.
            # Using tuples for 2D indexing
            read1 = (L_local_inner, PysmtCoordSet(i, Minus(j, Int(1))))
            read2 = (L_local_inner, PysmtCoordSet(Minus(j, Int(1)), Minus(j, Int(1))))
            write = (L_local_inner, PysmtCoordSet(i, j))

            b.add_compute("T_cholesky", reads=[read1, read2], writes=[write])
    return b.root_graph, outer_loop_node, inner_loop_node, N, L_root


def build_cholesky_full_kernel_graph():
    """
    Helper to create a P3G graph for the full Cholesky kernel.
    for i = 0 to N-1:
      for j = 0 to i:
        sum_val = 0
        for k = 0 to j-1:
          sum_val = sum_val + L[i,k] * L[j,k]
        L[i,j] = A[i,j] - sum_val
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)

    # Pysmt symbols for array content (needed for Select operations)
    A_val = Symbol("A_val", ArrayType(INT, INT))
    L_val = Symbol("L_val", ArrayType(INT, INT))

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
            (
                A_root,
                PysmtCoordSet(PysmtRange(Int(0), N), PysmtRange(Int(0), N)),
            ),  # Reads entire A
            (L_root, PysmtCoordSet(PysmtRange(Int(0), N), PysmtRange(Int(0), N))),
        ],  # Reads entire L
        writes=[(L_root, PysmtCoordSet(PysmtRange(Int(0), N), PysmtRange(Int(0), N)))],
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
                (
                    A_local_outer,
                    PysmtCoordSet(
                        PysmtRange(Int(0), Plus(i, Int(1))),
                        PysmtRange(Int(0), Plus(i, Int(1))),
                    ),
                ),
                # Reads A[0..i, 0..i]
                (
                    L_local_outer,
                    PysmtCoordSet(
                        PysmtRange(Int(0), Plus(i, Int(1))),
                        PysmtRange(Int(0), Plus(i, Int(1))),
                    ),
                ),
            ],
            # Reads L[0..i, 0..i]
            writes=[
                (
                    L_local_outer,
                    PysmtCoordSet(
                        PysmtRange(Int(0), Plus(i, Int(1))),
                        PysmtRange(Int(0), Plus(i, Int(1))),
                    ),
                )
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
                        PysmtCoordSet(
                            PysmtRange(Int(0), Plus(i, Int(1))),
                            PysmtRange(Int(0), Plus(j, Int(1))),
                        ),
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
                        (L_local_inner, PysmtCoordSet(i, k)),  # Read L[i,k]
                        (L_local_inner, PysmtCoordSet(j, k)),
                    ],  # Read L[j,k]
                    writes=[(sum_val_local_inner, Int(0))],  # Write new sum_val
                )

            # Final computation for L[i,j] = A[i,j] - sum_val (simplified)
            # This compute node is outside L_inner, but inside L_middle
            b.add_compute(
                "T_final_Lij",
                reads=[
                    (A_local_middle, PysmtCoordSet(i, j)),  # Read A[i,j]
                    (sum_val_scalar, Int(0)),  # Read final sum_val
                    (L_local_middle, PysmtCoordSet(j, j)),
                ],  # Read L[j,j] (for division, if modeled)
                writes=[(L_local_middle, PysmtCoordSet(i, j))],  # Write L[i,j]
            )
    return (
        b.root_graph,
        outer_loop_node,
        middle_loop_node,
        inner_loop_node,
        N,
        A_root,
        L_root,
        A_val,
        L_val,
    )


def build_data_aware_bi_graph():
    """
    Helper to create a P3G graph for a Data-Aware loop:
    for i = 1...N: if (B[i] > 0) then A[i] = A[i-1].
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")
    B_val = Symbol("B_val", ArrayType(INT, INT))

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[
            (A_root, PysmtRange(Int(0), Minus(N, Int(1)))),
            (B_root, PysmtRange(Int(1), N)),
        ],
        writes=[(A_root, PysmtRange(Int(1), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")

        with b.add_branch(
            "B1",
            reads=[(A_local, Minus(k, Int(1))), (B_local, k)],
            writes=[(A_local, k)],
        ) as B1:
            P1 = GT(Select(B_val, k), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1 = b.add_data("A", is_output=True)
                B_path1 = b.add_data("B")
                b.add_compute(
                    "T1_seq",
                    reads=[(B_path1, k), (A_path1, Minus(k, Int(1)))],
                    writes=[(A_path1, k)],
                )

        with b.add_branch("B2", reads=[(B_local, k)], writes=[]) as B2:
            P2 = LE(Select(B_val, k), Int(0))
            with B2.add_path(P2):
                # Data nodes local to this path's graph
                B_path2 = b.add_data("B")
                b.add_compute("T2_skip", reads=[(B_path2, k)], writes=[])
    return b.root_graph, loop_node, N, A_root, B_root, B_val


def build_data_aware_bi_b13_graph():
    """
    Helper to create a P3G graph for a Data-Aware loop:
    for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
    """
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
            (A_root, PysmtRange(Int(0), Minus(N, Int(1)))),
            (B_root, PysmtRange(Int(1), N)),
            (B_root, const_idx),
        ],
        writes=[(A_root, PysmtRange(Int(1), N))],
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
    return b.root_graph, loop_node, N, A_root, B_root, B_val, const_idx


def build_gauss_seidel_red_graph():
    """
    Helper to create a P3G graph for Gauss-Seidel Red Pass.
    // Red Pass (odd indices - parallel)
    for i = 1, 3, 5, ...:
        A[i] = A[i-1] + A[i+1]
    """
    b_red = GraphBuilder()
    N_red = b_red.add_symbol("N", INT)
    A_red = b_red.add_data("A", is_output=True)

    red_loop_node = None
    # Loop for k from 0 up to (N/2 - 1)
    loop_end_red_k = Minus(Div(N_red, Int(2)), Int(1))
    with b_red.add_loop(
        "L_red",
        "k",
        Int(0),
        loop_end_red_k,
        reads=[(A_red, PysmtRange(Int(0), Plus(N_red, Int(1))))],
        writes=[(A_red, PysmtRange(Int(1), N_red))],
    ) as L_red:
        k_red = L_red.loop_var
        red_loop_node = L_red

        # Original index i = 2*k + 1
        i = Plus(Times(Int(2), k_red), Int(1))

        # A[i] = A[i-1] + A[i+1]
        b_red.add_compute(
            "T_red",
            reads=[(A_red, Minus(i, Int(1))), (A_red, Plus(i, Int(1)))],
            writes=[(A_red, i)],
        )
    return b_red.root_graph, red_loop_node, N_red, A_red


def build_gauss_seidel_black_graph():
    """
    Helper to create a P3G graph for Gauss-Seidel Black Pass.
    // Black Pass (even indices - parallel)
    for i = 2, 4, 6, ...:
        A[i] = A[i-1] + A[i+1]
    """
    b_black = GraphBuilder()
    N_black = b_black.add_symbol("N", INT)
    A_black = b_black.add_data("A", is_output=True)

    black_loop_node = None
    # Loop for k from 0 up to (N/2 - 2)
    loop_end_black_k = Minus(Div(N_black, Int(2)), Int(2))
    with b_black.add_loop(
        "L_black",
        "k",
        Int(0),
        loop_end_black_k,
        reads=[(A_black, PysmtRange(Int(1), Plus(N_black, Int(1))))],
        writes=[(A_black, PysmtRange(Int(2), N_black))],
    ) as L_black:
        k_black = L_black.loop_var
        black_loop_node = L_black

        # Original index i = 2*k + 2
        i = Plus(Times(Int(2), k_black), Int(2))

        # A[i] = A[i-1] + A[i+1]
        b_black.add_compute(
            "T_black",
            reads=[(A_black, Minus(i, Int(1))), (A_black, Plus(i, Int(1)))],
            writes=[(A_black, i)],
        )
    return b_black.root_graph, black_loop_node, N_black, A_black


def build_gauss_seidel_traditional_graph():
    """
    Helper to create a P3G graph for Traditional 1D Gauss-Seidel.
    for i = 1 to N-1:
      A[i] = A[i-1] + A[i+1]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A = b.add_data("A", is_output=True)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        Minus(N, Int(1)),
        reads=[(A, PysmtRange(Int(0), N))],
        writes=[(A, PysmtRange(Int(1), Minus(N, Int(1))))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # A[i] = A[i-1] + A[i+1]
        b.add_compute(
            "T1", reads=[(A, Minus(k, Int(1))), (A, Plus(k, Int(1)))], writes=[(A, k)]
        )
    return b.root_graph, loop_node, N, A


def build_indirect_read_gather_graph():
    """
    Helper to create a P3G graph for Indirect Read (Gather) operation:
    for i = 1...N: A[i] = B[ IDX[i] ].
    """
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
        reads=[(B_root, PysmtRange(Int(0), N)), (IDX_root, PysmtRange(Int(0), N))],
        writes=[(A_root, PysmtRange(Int(0), N))],
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
    return b.root_graph, loop_node, N, A_root, B_root, IDX_root, IDX_val


def build_indirect_write_scatter_graph():
    """
    Helper to create a P3G graph for Indirect Write (Scatter) operation:
    for i = 1...N: A[ IDX[i] ] = B[i].
    """
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
        reads=[(B_root, PysmtRange(Int(0), N)), (IDX_root, PysmtRange(Int(0), N))],
        writes=[(A_root, PysmtRange(Int(0), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        IDX_local = b.add_data("IDX")

        write_idx = Select(IDX_val, k)

        b.add_compute(
            "T1_scatter",
            reads=[(B_local, k), (IDX_local, k)],
            writes=[(A_local, write_idx)],
        )
    return b.root_graph, loop_node, N, A_root, B_root, IDX_root, IDX_val


def build_long_distance_dependency_graph():
    """
    Helper to create a P3G graph for a loop with long-distance dependency:
    for i = 2...N: A[i] = A[max(i-10, 0)] + B[i].
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(2),
        N,
        reads=[(A_root, PysmtRange(Int(0), N)), (B_root, PysmtRange(Int(2), N))],
        writes=[(A_root, PysmtRange(Int(2), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")

        idx = Minus(k, Int(10))

        with b.add_branch(
            "B1", reads=[(A_local, idx), (B_local, k)], writes=[(A_local, k)]
        ) as B1:
            # if k - 10 > 0
            P1 = GT(Minus(k, Int(10)), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1 = b.add_data("A", is_output=True)
                B_path1 = b.add_data("B")
                b.add_compute(
                    "T1_gt", reads=[(A_path1, idx), (B_path1, k)], writes=[(A_path1, k)]
                )

        idx = Int(0)
        with b.add_branch(
            "B2", reads=[(A_local, idx), (B_local, k)], writes=[(A_local, k)]
        ) as B2:
            # else
            P2 = LE(Minus(k, Int(10)), Int(0))
            with B2.add_path(P2):
                # Data nodes local to this path's graph
                A_path2 = b.add_data("A", is_output=True)
                B_path2 = b.add_data("B")
                b.add_compute(
                    "T2_le", reads=[(A_path2, idx), (B_path2, k)], writes=[(A_path2, k)]
                )
    return b.root_graph, loop_node, N, A_root, B_root


def build_nested_loop_outer_dofs_graph():
    """
    Helper to create a P3G graph for a Nested Loop where the OUTER loop is DOFS:
    for i = 1...N:
      for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    M = b.add_symbol("M", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")

    loop_node = None
    L_inner_node = None

    with b.add_loop(
        "L_outer",
        "i",
        Int(1),
        N,
        reads=[
            (A_root, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M))),
            (B_root, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M))),
        ],
        writes=[(A_root, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M)))],
    ) as L_outer:
        i_sym = L_outer.loop_var
        loop_node = L_outer

        A_local_outer = b.add_data("A", is_output=True)
        B_local_outer = b.add_data("B")

        with b.add_loop(
            "L_inner",
            "j",
            Int(1),
            M,
            reads=[
                (A_local_outer, PysmtCoordSet(i_sym, PysmtRange(Int(1), M))),
                (
                    A_local_outer,
                    PysmtCoordSet(Minus(i_sym, Int(1)), PysmtRange(Int(1), M)),
                ),
                (B_local_outer, PysmtCoordSet(i_sym, PysmtRange(Int(1), M))),
            ],
            writes=[(A_local_outer, PysmtCoordSet(i_sym, PysmtRange(Int(1), M)))],
        ) as L_inner:
            j_sym = L_inner.loop_var
            L_inner_node = L_inner

            A_local_inner = b.add_data("A", is_output=True)
            B_local_inner = b.add_data("B")

            reads_A = (A_local_inner, PysmtCoordSet(Minus(i_sym, Int(1)), j_sym))
            reads_B = (B_local_inner, PysmtCoordSet(i_sym, j_sym))
            writes_A = (A_local_inner, PysmtCoordSet(i_sym, j_sym))

            b.add_compute("T_comp", reads=[reads_A, reads_B], writes=[writes_A])
    return b.root_graph, loop_node, L_inner_node, N, M, A_root, B_root


def build_nested_loop_inner_dofs_graph():
    """
    Helper to create a P3G graph for a Nested Loop with inner loop DOFS:
    for i = 1...N:
      for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    M = b.add_symbol("M", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")

    loop_node = None
    L_inner_node = None

    with b.add_loop(
        "L_outer",
        "i",
        Int(1),
        N,
        reads=[
            (A_root, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M))),
            (B_root, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M))),
        ],
        writes=[(A_root, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M)))],
    ) as L_outer:
        i_sym = L_outer.loop_var
        loop_node = L_outer

        A_local_outer = b.add_data("A", is_output=True)
        B_local_outer = b.add_data("B")

        with b.add_loop(
            "L_inner",
            "j",
            Int(1),
            M,
            reads=[
                (A_local_outer, PysmtCoordSet(i_sym, PysmtRange(Int(1), M))),
                (B_local_outer, PysmtCoordSet(i_sym, PysmtRange(Int(1), M))),
            ],
            writes=[(A_local_outer, PysmtCoordSet(i_sym, PysmtRange(Int(1), M)))],
        ) as L_inner:
            j_sym = L_inner.loop_var
            L_inner_node = L_inner

            A_local_inner = b.add_data("A", is_output=True)
            B_local_inner = b.add_data("B")

            b.add_compute(
                "T_comp",
                reads=[
                    (
                        A_local_inner,
                        PysmtCoordSet(i_sym, Minus(j_sym, Int(1))),
                    ),
                    (B_local_inner, PysmtCoordSet(i_sym, j_sym)),
                    (A_local_inner, PysmtCoordSet(i_sym, j_sym)),
                ],
                writes=[(A_local_inner, PysmtCoordSet(i_sym, j_sym))],
            )
    return b.root_graph, loop_node, L_inner_node, N, M, A_root, B_root


def build_non_linear_predicate_graph():
    """
    Helper to create a P3G graph for a loop with a Non-linear Predicate:
    for i=0:N {
      if i*i <= N: A[i] = B[i] + C[i]  // Parallel part
      else: A[i] = A[i-1] + C[i]       // Sequential part
    }
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")
    C_root = b.add_data("C")

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(0),
        N,
        reads=[
            (A_root, PysmtRange(Int(0), Minus(N, Int(1)))),
            (B_root, PysmtRange(Int(0), N)),
            (C_root, PysmtRange(Int(0), N)),
        ],
        writes=[(A_root, PysmtRange(Int(0), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        C_local = b.add_data("C")

        with b.add_branch(
            "B1", reads=[(B_local, k), (C_local, k)], writes=[(A_local, k)]
        ) as B1:
            P1 = LE(Times(k, k), N)
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1 = b.add_data("A", is_output=True)
                B_path1 = b.add_data("B")
                C_path1 = b.add_data("C")
                b.add_compute(
                    "T1_par", reads=[(B_path1, k), (C_path1, k)], writes=[(A_path1, k)]
                )

        with b.add_branch(
            "B2",
            reads=[
                (A_local, Minus(k, Int(1))),
                (A_local, k),
                (B_local, k),
                (C_local, k),
            ],
            writes=[(A_local, k)],
        ) as B2:
            P2 = GT(Times(k, k), N)
            with B2.add_path(P2):
                # Data nodes local to this path's graph
                A_path2 = b.add_data("A", is_output=True)
                C_path2 = b.add_data("C")
                b.add_compute(
                    "T2_seq",
                    reads=[(A_path2, Minus(k, Int(1))), (C_path2, k)],
                    writes=[(A_path2, k)],
                )
    return b.root_graph, loop_node, N, A_root, B_root, C_root


def build_non_linear_access_graph():
    """
    Helper to create a P3G graph for a loop with a Non-linear Array Access:
    for i=0:N: A[i*i] = B[i] + C[i]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")
    C_root = b.add_data("C")

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(0),
        N,
        reads=[
            (B_root, PysmtRange(Int(0), N)),
            (C_root, PysmtRange(Int(0), N)),
        ],
        writes=[
            (A_root, PysmtRange(Int(0), Times(N, N)))
        ],  # Upper bound for A[i*i] is N*N
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        C_local = b.add_data("C")

        # A[k*k] = B[k] + C[k]
        b.add_compute(
            "T1_comp",
            reads=[(B_local, k), (C_local, k)],
            writes=[(A_local, Times(k, k))],
        )
    return b.root_graph, loop_node, N, A_root, B_root, C_root


def build_non_linear_access_sequential_graph():
    """
    Helper to create a P3G graph for a loop with a Non-linear Array Access that is sequential:
    for i = 1...N: A[i*i] = A[(i-1)*(i-1)] + B[i]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[
            (
                A_root,
                PysmtRange(Int(0), Times(Minus(N, Int(1)), Minus(N, Int(1)))),
            ),  # Read from (i-1)*(i-1)
            (B_root, PysmtRange(Int(1), N)),
        ],
        writes=[(A_root, PysmtRange(Int(1), Times(N, N)))],  # Write to i*i
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")

        # A[k*k] = A[(k-1)*(k-1)] + B[k]
        b.add_compute(
            "T1_comp",
            reads=[(A_local, Times(Minus(k, Int(1)), Minus(k, Int(1)))), (B_local, k)],
            writes=[(A_local, Times(k, k))],
        )
    return b.root_graph, loop_node, N, A_root, B_root


def build_parallel_loop_graph():
    """
    Helper to create a P3G graph for a Parallel Loop: for i in 0:n { a[i] = b[i] + c[i] }.
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")
    C_root = b.add_data("C")

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(0),
        N,
        reads=[(B_root, PysmtRange(Int(0), N)), (C_root, PysmtRange(Int(0), N))],
        writes=[(A_root, PysmtRange(Int(0), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        C_local = b.add_data("C")

        b.add_compute("T1", reads=[(B_local, k), (C_local, k)], writes=[(A_local, k)])
    return b.root_graph, loop_node, N, A_root, B_root, C_root


def build_sequential_loop_graph():
    """
    Helper to create a P3G graph for a Sequential Loop: for i = 2...N: A[i] = A[i-1] + B[i].
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_root = b.add_data("A", is_output=True)
    B_root = b.add_data("B")

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(2),
        N,
        reads=[
            (A_root, PysmtRange(Int(1), Minus(N, Int(1)))),
            (B_root, PysmtRange(Int(2), N)),
        ],
        writes=[(A_root, PysmtRange(Int(2), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1
        A_local = b.add_data("A", is_output=True)
        B_local = b.add_data("B")
        b.add_compute(
            "T1",
            reads=[(A_local, Minus(k, Int(1))), (B_local, k)],
            writes=[(A_local, k)],
        )
    return b.root_graph, loop_node, N, A_root, B_root


def build_sequential_with_symbolic_max_index_graph():
    """
    Helper to create a P3G graph for a Sequential Loop with max(i-w, 0) index, where w is a symbolic variable.
    for i = 2...N: A[i] = A[max(i-w, 0)] + B[i]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    w = b.add_symbol("w", INT)
    A = b.add_data("A", is_output=True)
    B = b.add_data("B")

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(2),
        N,
        reads=[(A, PysmtRange(Int(0), N)), (B, PysmtRange(Int(2), N))],
        writes=[(A, PysmtRange(Int(2), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        with b.add_branch(
            "B1", reads=[(A, Minus(k, w)), (A, Int(0)), (B, k)], writes=[(A, k)]
        ) as B1:
            # if k - w > 0
            P1 = GT(Minus(k, w), Int(0))
            with B1.add_path(P1):
                idx = Minus(k, w)
                b.add_compute("T1_gt", reads=[(A, idx), (B, k)], writes=[(A, k)])
            # else
            P2 = LE(Minus(k, w), Int(0))
            with B1.add_path(P2):
                idx = Int(0)
                b.add_compute("T2_le", reads=[(A, idx), (B, k)], writes=[(A, k)])
    return b.root_graph, loop_node, N, w, A, B
