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
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)

    loop_node = None
    with b.add_loop(
        "L_k",
        "k",
        Int(0),
        Minus(N, Int(1)),
        reads=[(A_root_in, PysmtRange(Int(0), Minus(N, Int(1))))],
        writes=[(A_root_out, PysmtRange(Int(0), Minus(N, Int(1))))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        idx_rev = Minus(Minus(N, Int(1)), k)

        # Get local references to the data containers for this scope
        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)

        b.add_compute(
            "swap",
            reads=[(A_local_in, k), (A_local_in, idx_rev)],
            writes=[(A_local_out, k), (A_local_out, idx_rev)],
        )
    return b.root_graph, loop_node, N, A_root_in


def build_cholesky_sequential_graph():
    """
    Helper to create a P3G graph for a Cholesky Decomposition-like kernel.
    for i = 2...N:
      for j = 2...i:
        L[i, j] = L[i, j-1] + L[j-1, j-1]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    L_val = b.add_symbol("L_val", ArrayType(INT, INT))
    L_root_in, L_root_out = b.add_write_data("L", pysmt_array_sym=L_val)

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
                L_root_in,
                PysmtCoordSet(
                    PysmtRange(Int(1), N), PysmtRange(Int(1), Minus(N, Int(1)))
                ),
            ),
            (L_root_in, PysmtCoordSet(PysmtRange(Int(2), N), PysmtRange(Int(2), N))),
        ],
        writes=[
            (L_root_out, PysmtCoordSet(PysmtRange(Int(2), N), PysmtRange(Int(2), N)))
        ],
    ) as L_outer:
        i = L_outer.loop_var
        outer_loop_node = L_outer

        # Get local references to the data containers for this scope
        L_local_outer_in, L_local_outer_out = b.add_write_data(
            "L", pysmt_array_sym=L_val
        )

        with b.add_loop(
            "L_inner",
            "j",
            Int(2),
            i,
            reads=[
                (
                    L_local_outer_in,
                    PysmtCoordSet(
                        PysmtRange(Int(1), i), PysmtRange(Int(1), Minus(i, Int(1)))
                    ),
                ),
                (
                    L_local_outer_in,
                    PysmtCoordSet(PysmtRange(Int(2), i), PysmtRange(Int(2), i)),
                ),
            ],
            writes=[
                (
                    L_local_outer_out,
                    PysmtCoordSet(PysmtRange(Int(2), i), PysmtRange(Int(2), i)),
                )
            ],
        ) as L_inner:
            j = L_inner.loop_var
            inner_loop_node = L_inner

            # Get local references to the data containers for this scope
            L_local_inner_in, L_local_inner_out = b.add_write_data(
                "L", pysmt_array_sym=L_val
            )

            # L[i, j] = L[i, j-1] + L[j-1, j-1]
            # This models a RAW dependency on L[i, j-1] within the inner loop.
            # It also models a WAR/WAW dependency on L[j-1, j-1] across outer loop iterations.
            # Using tuples for 2D indexing
            b.add_compute(
                "T_cholesky",
                reads=[
                    (L_local_inner_in, PysmtCoordSet(i, Minus(j, Int(1)))),
                    (
                        L_local_inner_in,
                        PysmtCoordSet(Minus(j, Int(1)), Minus(j, Int(1))),
                    ),
                    (L_local_inner_in, PysmtCoordSet(i, j)),
                ],
                writes=[(L_local_inner_out, PysmtCoordSet(i, j))],
            )
    return b.root_graph, outer_loop_node, inner_loop_node, N, L_root_in


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
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    L_val = b.add_symbol("L_val", ArrayType(INT, INT))

    # Link Pysmt symbols to Data nodes
    A_root = b.add_read_data("A", pysmt_array_sym=A_val)
    L_root_in, L_root_out = b.add_write_data("L", pysmt_array_sym=L_val)

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
            (L_root_in, PysmtCoordSet(PysmtRange(Int(0), N), PysmtRange(Int(0), N))),
            (L_root_out, PysmtCoordSet(PysmtRange(Int(0), N), PysmtRange(Int(0), N))),
        ],  # Reads entire L
        writes=[
            (L_root_out, PysmtCoordSet(PysmtRange(Int(0), N), PysmtRange(Int(0), N)))
        ],
    ) as L_outer:  # Writes entire L
        i = L_outer.loop_var
        outer_loop_node = L_outer

        L_local_outer_in, L_local_outer_out = b.add_write_data(
            "L", pysmt_array_sym=L_val
        )
        A_local_outer_in = b.add_read_data("A", pysmt_array_sym=A_val)

        # Middle loop: for j = 0 to i
        with b.add_loop(
            "L_middle",
            "j",
            Int(0),
            i,
            reads=[
                (
                    A_local_outer_in,
                    PysmtCoordSet(
                        PysmtRange(Int(0), Plus(i, Int(1))),
                        PysmtRange(Int(0), Plus(i, Int(1))),
                    ),
                ),
                # Reads A[0..i, 0..i]
                (
                    L_local_outer_in,
                    PysmtCoordSet(
                        PysmtRange(Int(0), Plus(i, Int(1))),
                        PysmtRange(Int(0), Plus(i, Int(1))),
                    ),
                ),
                (
                    L_local_outer_out,
                    PysmtCoordSet(
                        PysmtRange(Int(0), Plus(i, Int(1))),
                        PysmtRange(Int(0), Plus(i, Int(1))),
                    ),
                ),
            ],
            # Reads L[0..i, 0..i]
            writes=[
                (
                    L_local_outer_out,
                    PysmtCoordSet(
                        PysmtRange(Int(0), Plus(i, Int(1))),
                        PysmtRange(Int(0), Plus(i, Int(1))),
                    ),
                )
            ],
        ) as L_middle:  # Writes L[0..i, 0..i]
            j = L_middle.loop_var
            middle_loop_node = L_middle

            L_local_middle_in, L_local_middle_out = b.add_write_data(
                "L", pysmt_array_sym=L_val
            )
            A_local_middle_in = b.add_read_data("A", pysmt_array_sym=A_val)

            # Scalar for sum_val
            sum_val_scalar_in, sum_val_scalar_out = b.add_write_data(
                "sum_val"
            )  # Scalar, so no pysmt_array_sym

            # Initialize sum_val = 0 (as a compute node)
            b.add_compute(
                "T_init_sum",
                reads=[(sum_val_scalar_out, Int(0))],
                writes=[(sum_val_scalar_out, Int(0))],  # Write 0 to sum_val
            )

            # Innermost loop: for k = 0 to j-1 (if j > 0)
            with b.add_loop(
                "L_inner",
                "k",
                Int(0),
                Minus(j, Int(1)),
                reads=[
                    (
                        L_local_middle_in,
                        PysmtCoordSet(
                            PysmtRange(Int(0), Plus(i, Int(1))),
                            PysmtRange(Int(0), Plus(j, Int(1))),
                        ),
                    ),
                    # Reads L[0..i, 0..j]
                    (sum_val_scalar_in, Int(0)),
                    (sum_val_scalar_out, Int(0)),
                ],  # Reads previous sum_val
                writes=[(sum_val_scalar_out, Int(0))],
            ) as L_inner:  # Writes new sum_val
                k = L_inner.loop_var
                inner_loop_node = L_inner

                L_local_inner_in = b.add_read_data("L", pysmt_array_sym=L_val)
                sum_val_local_inner_in, sum_val_local_inner_out = b.add_write_data(
                    "sum_val"
                )

                # Compute: sum_val = sum_val + L[i,k] * L[j,k]
                # We need to model the multiplication and addition.
                # For P3G, we just model the reads and writes.
                b.add_compute(
                    "T_sum_accum",
                    reads=[
                        (sum_val_local_inner_in, Int(0)),  # Read current sum_val
                        (L_local_inner_in, PysmtCoordSet(i, k)),  # Read L[i,k]
                        (L_local_inner_in, PysmtCoordSet(j, k)),
                        (sum_val_local_inner_out, Int(0)),
                    ],  # Read L[j,k]
                    writes=[(sum_val_local_inner_out, Int(0))],  # Write new sum_val
                )

            # Final computation for L[i,j] = A[i,j] - sum_val (simplified)
            # This compute node is outside L_inner, but inside L_middle
            b.add_compute(
                "T_final_Lij",
                reads=[
                    (A_local_middle_in, PysmtCoordSet(i, j)),  # Read A[i,j]
                    (sum_val_scalar_in, Int(0)),  # Read final sum_val
                    (L_local_middle_in, PysmtCoordSet(j, j)),
                    (L_local_middle_out, PysmtCoordSet(i, j)),
                ],  # Read L[j,j] (for division, if modeled)
                writes=[(L_local_middle_out, PysmtCoordSet(i, j))],  # Write L[i,j]
            )
    return (
        b.root_graph,
        outer_loop_node,
        middle_loop_node,
        inner_loop_node,
        N,
        A_root,
        L_root_in,
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
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[
            (A_root_in, PysmtRange(Int(0), Minus(N, Int(1)))),
            (A_root_in, PysmtRange(Int(1), N)),
            (B_root, PysmtRange(Int(1), N)),
        ],
        writes=[(A_root_out, PysmtRange(Int(1), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)

        with b.add_branch(
            "B1",
            reads=[(A_local_in, Minus(k, Int(1))), (A_local_in, k), (B_local_in, k)],
            writes=[(A_local_out, k)],
        ) as B1:
            P1 = GT(Select(B_val, k), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1_in, A_path1_out = b.add_write_data("A", pysmt_array_sym=A_val)
                b.add_compute(
                    "T1_seq",
                    reads=[(A_path1_in, Minus(k, Int(1))), (A_path1_in, k)],
                    writes=[(A_path1_out, k)],
                )

        with b.add_branch("B2", reads=[(B_local_in, k)], writes=[]) as B2:
            P2 = LE(Select(B_val, k), Int(0))
            with B2.add_path(P2):
                # Data nodes local to this path's graph
                b.add_compute("T2_skip", reads=[], writes=[])
    return b.root_graph, loop_node, N, A_root_in, B_root, B_val


def build_data_aware_bi_b13_graph():
    """
    Helper to create a P3G graph for a Data-Aware loop:
    for i = 1...N: if (B[i] - B[13] > 0) then A[i] = A[i-1].
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)

    const_idx = Int(13)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[
            (A_root_in, PysmtRange(Int(0), Minus(N, Int(1)))),
            (A_root_in, PysmtRange(Int(1), N)),
            (B_root, PysmtRange(Int(1), N)),
            (B_root, const_idx),
        ],
        writes=[(A_root_out, PysmtRange(Int(1), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)

        with b.add_branch(
            "B1",
            reads=[
                (A_local_in, Minus(k, Int(1))),
                (A_local_in, k),
                (B_local_in, k),
                (B_local_in, const_idx),
            ],
            writes=[(A_local_out, k)],
        ) as B1:
            val_k = Select(B_val, k)
            val_13 = Select(B_val, const_idx)

            P1 = GT(Minus(val_k, val_13), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1_in, A_path1_out = b.add_write_data("A", pysmt_array_sym=A_val)
                b.add_compute(
                    "T1_seq",
                    reads=[
                        (A_path1_in, Minus(k, Int(1))),
                        (A_path1_in, k),
                    ],
                    writes=[(A_path1_out, k)],
                )
    return b.root_graph, loop_node, N, A_root_in, B_root, B_val, const_idx


def build_gauss_seidel_red_graph():
    """
    Helper to create a P3G graph for Gauss-Seidel Red Pass.
    // Red Pass (odd indices - parallel)
    for i = 1, 3, 5, ...:
        A[i] = A[i-1] + A[i+1]
    """
    b_red = GraphBuilder()
    N_red = b_red.add_symbol("N", INT)
    A_val = b_red.add_symbol("A_val", ArrayType(INT, INT))
    A_red_root_in, A_red_root_out = b_red.add_write_data("A", pysmt_array_sym=A_val)

    red_loop_node = None
    # Loop for k from 0 up to (N/2 - 1)
    loop_end_red_k = Minus(Div(N_red, Int(2)), Int(1))
    with b_red.add_loop(
        "L_red",
        "k",
        Int(0),
        loop_end_red_k,
        reads=[
            (A_red_root_in, PysmtRange(Int(0), Plus(N_red, Int(1)))),
            (A_red_root_out, PysmtRange(Int(1), N_red)),
        ],
        writes=[(A_red_root_out, PysmtRange(Int(1), N_red))],
    ) as L_red:
        k_red = L_red.loop_var
        red_loop_node = L_red

        A_red_in, A_red_out = b_red.add_write_data("A", pysmt_array_sym=A_val)

        # Original index i = 2*k + 1
        i = Plus(Times(Int(2), k_red), Int(1))

        # A[i] = A[i-1] + A[i+1]
        b_red.add_compute(
            "T_red",
            reads=[
                (A_red_in, Minus(i, Int(1))),
                (A_red_in, Plus(i, Int(1))),
                (A_red_out, i),
            ],
            writes=[(A_red_out, i)],
        )
    return b_red.root_graph, red_loop_node, N_red, A_red_root_in


def build_gauss_seidel_black_graph():
    """
    Helper to create a P3G graph for Gauss-Seidel Black Pass.
    // Black Pass (even indices - parallel)
    for i = 2, 4, 6, ...:
        A[i] = A[i-1] + A[i+1]
    """
    b_black = GraphBuilder()
    N_black = b_black.add_symbol("N", INT)
    A_val = b_black.add_symbol("A_val", ArrayType(INT, INT))
    A_black_root_in, A_black_root_out = b_black.add_write_data(
        "A", pysmt_array_sym=A_val
    )

    black_loop_node = None
    # Loop for k from 0 up to (N/2 - 2)
    loop_end_black_k = Minus(Div(N_black, Int(2)), Int(2))
    with b_black.add_loop(
        "L_black",
        "k",
        Int(0),
        loop_end_black_k,
        reads=[
            (A_black_root_in, PysmtRange(Int(1), Plus(N_black, Int(1)))),
            (A_black_root_out, PysmtRange(Int(2), N_black)),
        ],
        writes=[(A_black_root_out, PysmtRange(Int(2), N_black))],
    ) as L_black:
        k_black = L_black.loop_var
        black_loop_node = L_black

        A_black_in, A_black_out = b_black.add_write_data("A", pysmt_array_sym=A_val)

        # Original index i = 2*k + 2
        i = Plus(Times(Int(2), k_black), Int(2))

        # A[i] = A[i-1] + A[i+1]
        b_black.add_compute(
            "T_black",
            reads=[
                (A_black_in, Minus(i, Int(1))),
                (A_black_in, Plus(i, Int(1))),
                (A_black_out, i),
            ],
            writes=[(A_black_out, i)],
        )
    return b_black.root_graph, black_loop_node, N_black, A_black_root_in


def build_gauss_seidel_traditional_graph():
    """
    Helper to create a P3G graph for Traditional 1D Gauss-Seidel.
    for i = 1 to N-1:
      A[i] = A[i-1] + A[i+1]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    A_in, A_out = b.add_write_data("A", pysmt_array_sym=A_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        Minus(N, Int(1)),
        reads=[
            (A_in, PysmtRange(Int(0), N)),
            (A_in, PysmtRange(Int(1), Minus(N, Int(1)))),
        ],
        writes=[(A_out, PysmtRange(Int(1), Minus(N, Int(1))))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)

        # A[i] = A[i-1] + A[i+1]
        b.add_compute(
            "T1",
            reads=[
                (A_local_in, Minus(k, Int(1))),
                (A_local_in, k),
                (A_local_in, Plus(k, Int(1))),
            ],
            writes=[(A_local_out, k)],
        )
    return b.root_graph, loop_node, N, A_in


def build_indirect_read_gather_graph():
    """
    Helper to create a P3G graph for Indirect Read (Gather) operation:
    for i = 1...N: A[i] = B[ IDX[i] ].
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    IDX_val = b.add_symbol("IDX_val", ArrayType(INT, INT))
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)
    IDX_root = b.add_read_data("IDX", pysmt_array_sym=IDX_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[
            (A_root_in, PysmtRange(Int(0), N)),
            (B_root, PysmtRange(Int(0), N)),
            (IDX_root, PysmtRange(Int(0), N)),
        ],
        writes=[(A_root_out, PysmtRange(Int(0), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)
        IDX_local_in = b.add_read_data("IDX", pysmt_array_sym=IDX_val)

        read_idx = Select(IDX_val, k)

        b.add_compute(
            "T1_gather",
            reads=[(A_local_in, k), (B_local_in, read_idx), (IDX_local_in, k)],
            writes=[(A_local_out, k)],
        )
    return b.root_graph, loop_node, N, A_root_in, B_root, IDX_root, IDX_val


def build_indirect_write_scatter_graph():
    """
    Helper to create a P3G graph for Indirect Write (Scatter) operation:
    for i = 1...N: A[ IDX[i] ] = B[i].
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)
    IDX_val = b.add_symbol("IDX_val", ArrayType(INT, INT))
    IDX_root = b.add_read_data("IDX", pysmt_array_sym=IDX_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[
            (A_root_in, PysmtRange(Int(0), N)),
            (B_root, PysmtRange(Int(0), N)),
            (IDX_root, PysmtRange(Int(0), N)),
        ],
        writes=[(A_root_out, PysmtRange(Int(0), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)
        IDX_local_in = b.add_read_data("IDX", pysmt_array_sym=IDX_val)

        write_idx = Select(IDX_val, k)

        b.add_compute(
            "T1_scatter",
            reads=[(B_local_in, k), (IDX_local_in, k), (A_local_in, write_idx)],
            writes=[(A_local_out, write_idx)],
        )
    return b.root_graph, loop_node, N, A_root_in, B_root, IDX_root, IDX_val


def build_long_distance_dependency_graph():
    """
    Helper to create a P3G graph for a loop with long-distance dependency:
    for i = 2...N: A[i] = A[max(i-10, 0)] + B[i].
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(2),
        N,
        reads=[
            (A_root_in, PysmtRange(Int(0), N)),
            (A_root_in, PysmtRange(Int(2), N)),
            (B_root, PysmtRange(Int(2), N)),
        ],
        writes=[(A_root_out, PysmtRange(Int(2), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)

        idx = Minus(k, Int(10))

        with b.add_branch(
            "B1",
            reads=[(A_local_in, idx), (A_local_in, k), (B_local_in, k)],
            writes=[(A_local_out, k)],
        ) as B1:
            # if k - 10 > 0
            P1 = GT(Minus(k, Int(10)), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1_in, A_path1_out = b.add_write_data("A", pysmt_array_sym=A_val)
                B_path1_in = b.add_read_data("B", pysmt_array_sym=B_val)
                b.add_compute(
                    "T1_gt",
                    reads=[(A_path1_in, idx), (A_path1_in, k), (B_path1_in, k)],
                    writes=[(A_path1_out, k)],
                )

        A_local_out = b.add_data("A", pysmt_array_sym=A_val)
        with b.add_branch(
            "B2",
            reads=[(A_local_in, Int(0)), (A_local_in, k), (B_local_in, k)],
            writes=[(A_local_out, k)],
        ) as B2:
            # else
            P2 = LE(Minus(k, Int(10)), Int(0))
            with B2.add_path(P2):
                # Data nodes local to this path's graph
                A_path2_in, A_path2_out = b.add_write_data("A", pysmt_array_sym=A_val)
                B_path2_in = b.add_read_data("B", pysmt_array_sym=B_val)
                b.add_compute(
                    "T2_le",
                    reads=[(A_path2_in, Int(0)), (A_path2_in, k), (B_path2_in, k)],
                    writes=[(A_path2_out, k)],
                )
    return b.root_graph, loop_node, N, A_root_in, B_root


def build_nested_loop_outer_dofs_graph():
    """
    Helper to create a P3G graph for a Nested Loop where the OUTER loop is DOFS:
    for i = 1...N:
      for j = 1...M: A[i, j] = A[i-1, j] + B[i, j]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    M = b.add_symbol("M", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)

    loop_node = None
    L_inner_node = None

    with b.add_loop(
        "L_outer",
        "i",
        Int(1),
        N,
        reads=[
            (A_root_in, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M))),
            (B_root, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M))),
        ],
        writes=[
            (A_root_out, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M)))
        ],
    ) as L_outer:
        i_sym = L_outer.loop_var
        loop_node = L_outer

        A_local_outer_in, A_local_outer_out = b.add_write_data(
            "A", pysmt_array_sym=A_val
        )
        B_local_outer_in = b.add_read_data("B", pysmt_array_sym=B_val)

        with b.add_loop(
            "L_inner",
            "j",
            Int(1),
            M,
            reads=[
                (A_local_outer_in, PysmtCoordSet(i_sym, PysmtRange(Int(1), M))),
                (
                    A_local_outer_in,
                    PysmtCoordSet(Minus(i_sym, Int(1)), PysmtRange(Int(1), M)),
                ),
                (B_local_outer_in, PysmtCoordSet(i_sym, PysmtRange(Int(1), M))),
            ],
            writes=[(A_local_outer_out, PysmtCoordSet(i_sym, PysmtRange(Int(1), M)))],
        ) as L_inner:
            j_sym = L_inner.loop_var
            L_inner_node = L_inner

            A_local_inner_in, A_local_inner_out = b.add_write_data(
                "A", pysmt_array_sym=A_val
            )
            B_local_inner_in = b.add_read_data("B", pysmt_array_sym=B_val)

            b.add_compute(
                "T_comp",
                reads=[
                    (A_local_inner_in, PysmtCoordSet(Minus(i_sym, Int(1)), j_sym)),
                    (B_local_inner_in, PysmtCoordSet(i_sym, j_sym)),
                    (A_local_inner_in, PysmtCoordSet(i_sym, j_sym)),
                ],
                writes=[(A_local_inner_out, PysmtCoordSet(i_sym, j_sym))],
            )
    return b.root_graph, loop_node, L_inner_node, N, M, A_root_in, B_root


def build_nested_loop_inner_dofs_graph():
    """
    Helper to create a P3G graph for a Nested Loop with inner loop DOFS:
    for i = 1...N:
      for j = 1...M: A[i, j] = A[i, j-1] + B[i, j]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    M = b.add_symbol("M", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)

    loop_node = None
    L_inner_node = None

    with b.add_loop(
        "L_outer",
        "i",
        Int(1),
        N,
        reads=[
            (A_root_in, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M))),
            (B_root, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M))),
        ],
        writes=[
            (A_root_out, PysmtCoordSet(PysmtRange(Int(1), N), PysmtRange(Int(1), M)))
        ],
    ) as L_outer:
        i_sym = L_outer.loop_var
        loop_node = L_outer

        A_local_outer_in, A_local_outer_out = b.add_write_data(
            "A", pysmt_array_sym=A_val
        )
        B_local_outer_in = b.add_read_data("B", pysmt_array_sym=B_val)

        with b.add_loop(
            "L_inner",
            "j",
            Int(1),
            M,
            reads=[
                (A_local_outer_in, PysmtCoordSet(i_sym, PysmtRange(Int(1), M))),
                (B_local_outer_in, PysmtCoordSet(i_sym, PysmtRange(Int(1), M))),
            ],
            writes=[(A_local_outer_out, PysmtCoordSet(i_sym, PysmtRange(Int(1), M)))],
        ) as L_inner:
            j_sym = L_inner.loop_var
            L_inner_node = L_inner

            A_local_inner_in, A_local_inner_out = b.add_write_data(
                "A", pysmt_array_sym=A_val
            )
            B_local_inner_in = b.add_read_data("B", pysmt_array_sym=B_val)

            b.add_compute(
                "T_comp",
                reads=[
                    (
                        A_local_inner_in,
                        PysmtCoordSet(i_sym, Minus(j_sym, Int(1))),
                    ),
                    (A_local_inner_in, PysmtCoordSet(i_sym, j_sym)),
                    (B_local_inner_in, PysmtCoordSet(i_sym, j_sym)),
                ],
                writes=[(A_local_inner_out, PysmtCoordSet(i_sym, j_sym))],
            )
    return b.root_graph, loop_node, L_inner_node, N, M, A_root_in, B_root


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
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    C_val = b.add_symbol("C_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)
    C_root = b.add_read_data("C", pysmt_array_sym=C_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(0),
        N,
        reads=[
            (A_root_in, PysmtRange(Int(0), Minus(N, Int(1)))),
            (B_root, PysmtRange(Int(0), N)),
            (C_root, PysmtRange(Int(0), N)),
            (A_root_out, PysmtRange(Int(0), N)),
        ],
        writes=[(A_root_out, PysmtRange(Int(0), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)
        C_local_in = b.add_read_data("C", pysmt_array_sym=C_val)

        with b.add_branch(
            "B1",
            reads=[(B_local_in, k), (C_local_in, k), (A_local_out, k)],
            writes=[(A_local_out, k)],
        ) as B1:
            P1 = LE(Times(k, k), N)
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1_in, A_path1_out = b.add_write_data("A", pysmt_array_sym=A_val)
                B_path1_in = b.add_read_data("B", pysmt_array_sym=B_val)
                C_path1_in = b.add_read_data("C", pysmt_array_sym=C_val)
                b.add_compute(
                    "T1_par",
                    reads=[(A_path1_in, k), (B_path1_in, k), (C_path1_in, k)],
                    writes=[(A_path1_out, k)],
                )

        with b.add_branch(
            "B2",
            reads=[
                (A_local_in, Minus(k, Int(1))),
                (A_local_in, k),
                (B_local_in, k),
                (C_local_in, k),
                (A_local_out, k),
            ],
            writes=[(A_local_out, k)],
        ) as B2:
            P2 = GT(Times(k, k), N)
            with B2.add_path(P2):
                # Data nodes local to this path's graph
                A_path2_in, A_path2_out = b.add_write_data("A", pysmt_array_sym=A_val)
                C_path2_in = b.add_read_data("C", pysmt_array_sym=C_val)
                b.add_compute(
                    "T2_seq",
                    reads=[
                        (A_path2_in, Minus(k, Int(1))),
                        (C_path2_in, k),
                        (A_path2_out, k),
                    ],
                    writes=[(A_path2_out, k)],
                )
    return b.root_graph, loop_node, N, A_root_in, B_root, C_root


def build_non_linear_access_graph():
    """
    Helper to create a P3G graph for a loop with a Non-linear Array Access:
    for i=0:N: A[i*i] = B[i] + C[i]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    C_val = b.add_symbol("C_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)
    C_root = b.add_read_data("C", pysmt_array_sym=C_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(0),
        N,
        reads=[
            (B_root, PysmtRange(Int(0), N)),
            (C_root, PysmtRange(Int(0), N)),
            (A_root_out, PysmtRange(Int(0), Times(N, N))),
        ],
        writes=[
            (A_root_out, PysmtRange(Int(0), Times(N, N)))
        ],  # Upper bound for A[i*i] is N*N
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        # Get local references to the data containers for this scope
        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)
        C_local_in = b.add_read_data("C", pysmt_array_sym=C_val)

        # A[k*k] = B[k] + C[k]
        b.add_compute(
            "T1_comp",
            reads=[(A_local_in, Times(k, k)), (B_local_in, k), (C_local_in, k)],
            writes=[(A_local_out, Times(k, k))],
        )
    return b.root_graph, loop_node, N, A_root_in, B_root, C_root


def build_non_linear_access_sequential_graph():
    """
    Helper to create a P3G graph for a loop with a Non-linear Array Access that is sequential:
    for i = 1...N: A[i*i] = A[(i-1)*(i-1)] + B[i]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(1),
        N,
        reads=[
            (
                A_root_in,
                PysmtRange(Int(0), Times(Minus(N, Int(1)), Minus(N, Int(1)))),
            ),  # Read from (i-1)*(i-1)
            (B_root, PysmtRange(Int(1), N)),
            (A_root_out, PysmtRange(Int(1), Times(N, N))),
        ],
        writes=[(A_root_out, PysmtRange(Int(1), Times(N, N)))],  # Write to i*i
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)

        # A[k*k] = A[(k-1)*(k-1)] + B[k]
        b.add_compute(
            "T1_comp",
            reads=[
                (A_local_in, Times(Minus(k, Int(1)), Minus(k, Int(1)))),
                (B_local_in, k),
                (A_local_out, Times(k, k)),
            ],
            writes=[(A_local_out, Times(k, k))],
        )
    return b.root_graph, loop_node, N, A_root_in, B_root


def build_parallel_loop_graph():
    """
    Helper to create a P3G graph for a Parallel Loop: for i in 0:n { a[i] = b[i] + c[i] }.
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    C_val = b.add_symbol("C_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)
    C_root = b.add_read_data("C", pysmt_array_sym=C_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(0),
        N,
        reads=[
            (A_root_in, PysmtRange(Int(0), N)),
            (B_root, PysmtRange(Int(0), N)),
            (C_root, PysmtRange(Int(0), N)),
        ],
        writes=[(A_root_out, PysmtRange(Int(0), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)
        C_local_in = b.add_read_data("C", pysmt_array_sym=C_val)

        b.add_compute(
            "T1",
            reads=[(A_local_in, k), (B_local_in, k), (C_local_in, k)],
            writes=[(A_local_out, k)],
        )
    return b.root_graph, loop_node, N, A_root_in, B_root, C_root


def build_sequential_loop_graph():
    """
    Helper to create a P3G graph for a Sequential Loop: for i = 2...N: A[i] = A[i-1] + B[i].
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(2),
        N,
        reads=[
            (A_root_in, PysmtRange(Int(1), Minus(N, Int(1)))),
            (A_root_in, PysmtRange(Int(2), N)),
            (B_root, PysmtRange(Int(2), N)),
        ],
        writes=[(A_root_out, PysmtRange(Int(2), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1
        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)
        b.add_compute(
            "T1",
            reads=[(A_local_in, Minus(k, Int(1))), (A_local_in, k), (B_local_in, k)],
            writes=[(A_local_out, k)],
        )
    return b.root_graph, loop_node, N, A_root_in, B_root


def build_sequential_with_symbolic_max_index_graph():
    """
    Helper to create a P3G graph for a Sequential Loop with max(i-w, 0) index, where w is a symbolic variable.
    for i = 2...N: A[i] = A[max(i-w, 0)] + B[i]
    """
    b = GraphBuilder()
    N = b.add_symbol("N", INT)
    w = b.add_symbol("w", INT)
    A_val = b.add_symbol("A_val", ArrayType(INT, INT))
    B_val = b.add_symbol("B_val", ArrayType(INT, INT))
    A_root_in, A_root_out = b.add_write_data("A", pysmt_array_sym=A_val)
    B_root = b.add_read_data("B", pysmt_array_sym=B_val)

    loop_node = None
    with b.add_loop(
        "L1",
        "k",
        Int(2),
        N,
        reads=[
            (A_root_in, PysmtRange(Int(0), N)),
            (A_root_in, PysmtRange(Int(2), N)),
            (B_root, PysmtRange(Int(2), N)),
        ],
        writes=[(A_root_out, PysmtRange(Int(2), N))],
    ) as L1:
        k = L1.loop_var
        loop_node = L1

        A_local_in, A_local_out = b.add_write_data("A", pysmt_array_sym=A_val)
        B_local_in = b.add_read_data("B", pysmt_array_sym=B_val)
        with b.add_branch(
            "B1",
            reads=[(A_local_in, Minus(k, w)), (A_local_in, k), (B_local_in, k)],
            writes=[(A_local_out, k)],
        ) as B1:
            # if k - w > 0
            P1 = GT(Minus(k, w), Int(0))
            with B1.add_path(P1):
                # Data nodes local to this path's graph
                A_path1_in, A_path1_out = b.add_write_data("A", pysmt_array_sym=A_val)
                B_path1_in = b.add_read_data("B", pysmt_array_sym=B_val)
                b.add_compute(
                    "T1_gt",
                    reads=[
                        (A_path1_in, Minus(k, w)),
                        (A_path1_in, k),
                        (B_path1_in, k),
                    ],
                    writes=[(A_path1_out, k)],
                )

        A_local_out = b.add_data("A", pysmt_array_sym=A_val)
        with b.add_branch(
            "B2",
            reads=[(A_local_in, Int(0)), (A_local_in, k), (B_local_in, k)],
            writes=[(A_local_out, k)],
        ) as B2:
            # else
            P2 = LE(Minus(k, w), Int(0))
            with B2.add_path(P2):
                # Data nodes local to this path's graph
                A_path2_in, A_path2_out = b.add_write_data("A", pysmt_array_sym=A_val)
                B_path2_in = b.add_read_data("B", pysmt_array_sym=B_val)
                b.add_compute(
                    "T2_le",
                    reads=[(A_path2_in, Int(0)), (A_path2_in, k), (B_path2_in, k)],
                    writes=[(A_path2_out, k)],
                )
    return b.root_graph, loop_node, N, w, A_root_in, B_root
