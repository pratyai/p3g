import argparse
import os
import sys
import pathlib
from copy import deepcopy

import dace
from dace.sdfg import SDFG, InterstateEdge
from dace.memlet import Memlet
from dace.sdfg.state import LoopRegion
from dace.transformation.interstate import LoopToMap
from dace.transformation.passes.fusion_inline import InlineSDFGs

from tools.array_ssa import expand_scalars

# Ensure we can run this script from anywhere within the project
# by adding the project root to sys.path
script_dir = os.path.dirname(os.path.abspath(__file__))
# Assuming the script is in tools/, the project root is one level up
project_root = os.path.abspath(os.path.join(script_dir, os.pardir))
if project_root not in sys.path:
    sys.path.insert(0, project_root)


def generate_heat3d_sdfg(name: str = "heat3d") -> SDFG:
    """
    Generates an SDFG for the Heat3D stencil application using nested LoopRegions.
    """
    # Define symbols
    N = dace.symbol("N", dace.int64)
    TSTEPS = dace.symbol("TSTEPS", dace.int64)

    # Create SDFG
    sdfg = SDFG(name)
    sdfg.add_array("A", [N, N, N], dace.float64)
    sdfg.add_array("B", [N, N, N], dace.float64)

    # Init State
    init_state = sdfg.add_state("init", is_start_block=True)

    # Time Loop
    time_loop = LoopRegion(
        label="time_loop",
        condition_expr="t < TSTEPS",
        loop_var="t",
        initialize_expr="t = 1",
        update_expr="t = t + 1",
    )
    sdfg.add_node(time_loop)
    sdfg.add_edge(init_state, time_loop, InterstateEdge())

    def create_spatial_nest(parent_region, prefix, input_arr, output_arr):
        # Create nested loops for i, j, k
        loops = []
        for var in ["i", "j", "k"]:
            loop = LoopRegion(
                label=f"{prefix}_{var}_loop",
                condition_expr=f"{var} < N-1",
                loop_var=var,
                initialize_expr=f"{var} = 1",
                update_expr=f"{var} = {var} + 1",
            )
            if not loops:
                parent_region.add_node(loop)
            else:
                loops[-1].add_node(loop, is_start_block=True)
            loops.append(loop)

        # Computation State inside the innermost loop (k_loop)
        k_loop = loops[-1]
        comp_state = k_loop.add_state(f"{prefix}_compute", is_start_block=True)

        tasklet = comp_state.add_tasklet(
            f"{prefix}_stencil",
            {"c", "xm", "xp", "ym", "yp", "zm", "zp"},
            {"res"},
            "res = 0.125 * (xm + xp + ym + yp + zm + zp) + 0.25 * c",
        )

        read_node = comp_state.add_read(input_arr)
        write_node = comp_state.add_write(output_arr)

        # Connect inputs
        inputs = [
            ("c", "i, j, k"),
            ("xm", "i-1, j, k"),
            ("xp", "i+1, j, k"),
            ("ym", "i, j-1, k"),
            ("yp", "i, j+1, k"),
            ("zm", "i, j, k-1"),
            ("zp", "i, j, k+1"),
        ]
        for conn, idx in inputs:
            comp_state.add_memlet_path(
                read_node, tasklet, dst_conn=conn, memlet=Memlet(f"{input_arr}[{idx}]")
            )

        # Connect output
        comp_state.add_memlet_path(
            tasklet, write_node, src_conn="res", memlet=Memlet(f"{output_arr}[i, j, k]")
        )

        return loops[0]

    # Create loop nests
    i_loop_b = create_spatial_nest(time_loop, "update_B", "A", "B")
    i_loop_a = create_spatial_nest(time_loop, "update_A", "B", "A")

    # Connect loops sequentially
    time_loop.add_edge(i_loop_b, i_loop_a, InterstateEdge())
    time_loop.start_block = time_loop.nodes().index(i_loop_b)

    # Final State
    final_state = sdfg.add_state("final")
    sdfg.add_edge(time_loop, final_state, InterstateEdge())

    return sdfg


def generate_spmv_sdfg(name: str = "spmv") -> SDFG:
    """
    Generates an SDFG for Sparse Matrix-Vector Multiplication (SpMV) using
    nested LoopRegions. This demonstrates control flow loops and the need
    for scalar expansion on 'accum' and bound variables.
    """
    M = dace.symbol("M", dace.int64)
    N = dace.symbol("N", dace.int64)
    nnz = dace.symbol("nnz", dace.int64)

    sdfg = SDFG(name)
    sdfg.add_array("A_row", [M + 1], dace.uint32)
    sdfg.add_array("A_col", [nnz], dace.uint32)
    sdfg.add_array("A", [nnz], dace.float64)  # Original name was A_val
    sdfg.add_array("x", [N], dace.float64)
    sdfg.add_array("y", [M], dace.float64)

    # Scalars for control flow and accumulation
    sdfg.add_scalar("start", dace.uint32, transient=True)
    sdfg.add_scalar("stop", dace.uint32, transient=True)
    sdfg.add_scalar("accum", dace.float64, transient=True)

    # Init State
    init_state = sdfg.add_state("init", is_start_block=True)

    # Outer Loop (i: 0 to M)
    i_loop = LoopRegion(
        label="i_loop",
        condition_expr="i < M",
        loop_var="i",
        initialize_expr="i = 0",
        update_expr="i = i + 1",
    )
    sdfg.add_node(i_loop)
    sdfg.add_edge(init_state, i_loop, InterstateEdge())

    # --- Inside i_loop ---

    # 1. Row Setup State: Read bounds and zero accum
    row_setup_state = i_loop.add_state("row_setup", is_start_block=True)

    # Tasklet for 'start'
    t_setup_start = row_setup_state.add_tasklet(
        "setup_start", {"r_start"}, {"s_out"}, "s_out = r_start;"
    )

    # Tasklet for 'stop'
    t_setup_stop = row_setup_state.add_tasklet(
        "setup_stop", {"r_end"}, {"e_out"}, "e_out = r_end;"
    )

    # Tasklet for 'accum'
    t_setup_accum = row_setup_state.add_tasklet(
        "setup_accum", {}, {"acc_out"}, "acc_out = 0.0"
    )

    # Read A_row[i], A_row[i+1]
    row_setup_state.add_memlet_path(
        row_setup_state.add_read("A_row"),
        t_setup_start,
        dst_conn="r_start",
        memlet=Memlet("A_row[i]"),
    )
    row_setup_state.add_memlet_path(
        row_setup_state.add_read("A_row"),
        t_setup_stop,
        dst_conn="r_end",
        memlet=Memlet("A_row[i+1]"),
    )

    # Write to scalars
    row_setup_state.add_memlet_path(
        t_setup_start,
        row_setup_state.add_write("start"),
        src_conn="s_out",
        memlet=Memlet("start[0]"),
    )
    row_setup_state.add_memlet_path(
        t_setup_stop,
        row_setup_state.add_write("stop"),
        src_conn="e_out",
        memlet=Memlet("stop[0]"),
    )
    row_setup_state.add_memlet_path(
        t_setup_accum,
        row_setup_state.add_write("accum"),
        src_conn="acc_out",
        memlet=Memlet("accum[0]"),
    )

    # 2. Inner Loop (k: start to stop)
    # We use symbols k_begin/k_end laundered from start/stop data
    k_loop = LoopRegion(
        label="k_loop",
        condition_expr="k < k_end",
        loop_var="k",
        initialize_expr="k = k_begin",
        update_expr="k = k + 1",
    )
    i_loop.add_node(k_loop)

    # Edge from Setup -> Inner Loop (Launder symbols)
    i_loop.add_edge(
        row_setup_state,
        k_loop,
        InterstateEdge(assignments={"k_begin": "start", "k_end": "stop"}),
    )

    # --- Inside k_loop ---

    # Compute State: accum += A_val[k] * x[A_col[k]]
    compute_state = k_loop.add_state("compute", is_start_block=True)

    # Tasklet for MAC + Indirection
    # x_val = x[col_idx] is handled by passing x array and index to tasklet
    t_mac = compute_state.add_tasklet(
        "mac",
        {"aval", "acol", "x_arr", "acc_in"},
        {"acc_out"},
        "acc_out = acc_in + aval * x_arr[acol]",
    )

    # Reads
    compute_state.add_memlet_path(
        compute_state.add_read("A"),
        t_mac,
        dst_conn="aval",
        memlet=Memlet("A[k]"),
    )
    compute_state.add_memlet_path(
        compute_state.add_read("A_col"),
        t_mac,
        dst_conn="acol",
        memlet=Memlet("A_col[k]"),
    )
    compute_state.add_memlet_path(
        compute_state.add_read("x"), t_mac, dst_conn="x_arr", memlet=Memlet("x[0:N]")
    )
    compute_state.add_memlet_path(
        compute_state.add_read("accum"),
        t_mac,
        dst_conn="acc_in",
        memlet=Memlet("accum[0]"),
    )

    # Write
    compute_state.add_memlet_path(
        t_mac,
        compute_state.add_write("accum"),
        src_conn="acc_out",
        memlet=Memlet("accum[0]"),
    )

    # 3. Row Write State (Back in i_loop, after k_loop)
    row_write_state = i_loop.add_state("row_write")
    i_loop.add_edge(k_loop, row_write_state, InterstateEdge())

    # Explicit copy tasklet for accum to y[i]
    t_copy_accum_to_y = row_write_state.add_tasklet(
        "copy_accum_to_y", {"acc_in"}, {"y_out"}, "y_out = acc_in"
    )

    # Connect read accum to tasklet input
    row_write_state.add_memlet_path(
        row_write_state.add_read("accum"),
        t_copy_accum_to_y,
        dst_conn="acc_in",
        memlet=Memlet("accum[0]"),
    )

    # Connect tasklet output to write y[i]
    row_write_state.add_memlet_path(
        t_copy_accum_to_y,
        row_write_state.add_write("y"),
        src_conn="y_out",
        memlet=Memlet("y[i]", subset="0"),
    )

    # Final state in SDFG
    final_state = sdfg.add_state("final")
    sdfg.add_edge(i_loop, final_state, InterstateEdge())

    return sdfg


def generate_gram_schmidt_sdfg(name: str = "gram_schmidt") -> SDFG:
    """
    Generates an SDFG for Gram-Schmidt Orthogonalization (MGS).
    Uses LoopRegions to expose scalar 'nrm' for SSA expansion.
    """
    M = dace.symbol("M", dace.int64)
    N = dace.symbol("N", dace.int64)

    sdfg = SDFG(name)
    sdfg.add_array("A", [M, N], dace.float64)
    sdfg.add_array("Q", [M, N], dace.float64)
    sdfg.add_array("R", [N, N], dace.float64)
    sdfg.add_scalar("nrm", dace.float64, transient=True)
    sdfg.add_scalar("tmp_dot", dace.float64, transient=True)  # For R[k, j]

    init_state = sdfg.add_state("init", is_start_block=True)

    # k loop: 0 to N
    k_loop = LoopRegion("k_loop", "k < N", "k", "k = 0", "k = k + 1")
    sdfg.add_node(k_loop)
    sdfg.add_edge(init_state, k_loop, InterstateEdge())

    # --- Inside k_loop ---

    # 1. Norm Calculation: nrm = dot(A[:, k], A[:, k])
    #    We need a loop over i (0 to M)
    nrm_init = k_loop.add_state("nrm_init", is_start_block=True)
    t_nrm_zero = nrm_init.add_tasklet("zero_nrm", {}, {"o"}, "o = 0.0")
    nrm_init.add_memlet_path(
        t_nrm_zero, nrm_init.add_write("nrm"), src_conn="o", memlet=Memlet("nrm[0]")
    )

    nrm_loop = LoopRegion("nrm_loop", "i_nrm < M", "i_nrm", "i_nrm=0", "i_nrm=i_nrm+1")
    k_loop.add_node(nrm_loop)
    k_loop.add_edge(nrm_init, nrm_loop, InterstateEdge())

    # Inside nrm_loop: nrm += A[i, k] * A[i, k]
    nrm_comp = nrm_loop.add_state("nrm_comp", is_start_block=True)
    t_nrm_acc = nrm_comp.add_tasklet(
        "nrm_acc", {"a", "acc_in"}, {"acc_out"}, "acc_out = acc_in + a * a"
    )
    nrm_comp.add_memlet_path(
        nrm_comp.add_read("A"), t_nrm_acc, dst_conn="a", memlet=Memlet("A[i_nrm, k]")
    )
    nrm_comp.add_memlet_path(
        nrm_comp.add_read("nrm"), t_nrm_acc, dst_conn="acc_in", memlet=Memlet("nrm[0]")
    )
    nrm_comp.add_memlet_path(
        t_nrm_acc,
        nrm_comp.add_write("nrm"),
        src_conn="acc_out",
        memlet=Memlet("nrm[0]"),
    )

    # 2. R[k, k] = sqrt(nrm) and Q[:, k] = A[:, k] / R[k, k]
    #    We compute R[k,k] first
    calc_rkk = k_loop.add_state("calc_rkk")
    k_loop.add_edge(nrm_loop, calc_rkk, InterstateEdge())

    t_rkk = calc_rkk.add_tasklet("rkk", {"n"}, {"r"}, "r = sqrt(n)")
    calc_rkk.add_memlet_path(
        calc_rkk.add_read("nrm"), t_rkk, dst_conn="n", memlet=Memlet("nrm[0]")
    )
    calc_rkk.add_memlet_path(
        t_rkk, calc_rkk.add_write("R"), src_conn="r", memlet=Memlet("R[k, k]")
    )

    #    Update Q[:, k] (Loop i)
    #    We need R[k, k] which is in array R.
    q_loop = LoopRegion("q_loop", "i_q < M", "i_q", "i_q=0", "i_q=i_q+1")
    k_loop.add_node(q_loop)
    k_loop.add_edge(calc_rkk, q_loop, InterstateEdge())

    q_comp = q_loop.add_state("q_comp", is_start_block=True)
    t_q = q_comp.add_tasklet("calc_q", {"a", "r"}, {"q"}, "q = a / r")
    q_comp.add_memlet_path(
        q_comp.add_read("A"), t_q, dst_conn="a", memlet=Memlet("A[i_q, k]")
    )
    q_comp.add_memlet_path(
        q_comp.add_read("R"), t_q, dst_conn="r", memlet=Memlet("R[k, k]")
    )
    q_comp.add_memlet_path(
        t_q, q_comp.add_write("Q"), src_conn="q", memlet=Memlet("Q[i_q, k]")
    )

    # 3. Inner j loop: k+1 to N
    j_loop = LoopRegion("j_loop", "j < N", "j", "j = k + 1", "j = j + 1")
    k_loop.add_node(j_loop)
    k_loop.add_edge(q_loop, j_loop, InterstateEdge())

    # --- Inside j_loop ---

    # 3a. R[k, j] = dot(Q[:, k], A[:, j]) using tmp_dot scalar
    dot_init = j_loop.add_state("dot_init", is_start_block=True)
    t_dot_zero = dot_init.add_tasklet("zero_dot", {}, {"o"}, "o = 0.0")
    dot_init.add_memlet_path(
        t_dot_zero,
        dot_init.add_write("tmp_dot"),
        src_conn="o",
        memlet=Memlet("tmp_dot[0]"),
    )

    dot_loop = LoopRegion("dot_loop", "i_dot < M", "i_dot", "i_dot=0", "i_dot=i_dot+1")
    j_loop.add_node(dot_loop)
    j_loop.add_edge(dot_init, dot_loop, InterstateEdge())

    dot_comp = dot_loop.add_state("dot_comp", is_start_block=True)
    t_dot_acc = dot_comp.add_tasklet(
        "dot_acc", {"q", "a", "acc_in"}, {"acc_out"}, "acc_out = acc_in + q * a"
    )
    dot_comp.add_memlet_path(
        dot_comp.add_read("Q"), t_dot_acc, dst_conn="q", memlet=Memlet("Q[i_dot, k]")
    )
    dot_comp.add_memlet_path(
        dot_comp.add_read("A"), t_dot_acc, dst_conn="a", memlet=Memlet("A[i_dot, j]")
    )
    dot_comp.add_memlet_path(
        dot_comp.add_read("tmp_dot"),
        t_dot_acc,
        dst_conn="acc_in",
        memlet=Memlet("tmp_dot[0]"),
    )
    dot_comp.add_memlet_path(
        t_dot_acc,
        dot_comp.add_write("tmp_dot"),
        src_conn="acc_out",
        memlet=Memlet("tmp_dot[0]"),
    )

    # Save tmp_dot to R[k, j]
    save_dot = j_loop.add_state("save_dot")
    j_loop.add_edge(dot_loop, save_dot, InterstateEdge())
    t_save = save_dot.add_tasklet("save", {"i"}, {"o"}, "o = i")
    save_dot.add_memlet_path(
        save_dot.add_read("tmp_dot"), t_save, dst_conn="i", memlet=Memlet("tmp_dot[0]")
    )
    save_dot.add_memlet_path(
        t_save, save_dot.add_write("R"), src_conn="o", memlet=Memlet("R[k, j]")
    )

    # 3b. A[:, j] -= Q[:, k] * R[k, j] (Loop i)
    sub_loop = LoopRegion("sub_loop", "i_sub < M", "i_sub", "i_sub=0", "i_sub=i_sub+1")
    j_loop.add_node(sub_loop)
    j_loop.add_edge(save_dot, sub_loop, InterstateEdge())

    sub_comp = sub_loop.add_state("sub_comp", is_start_block=True)
    t_sub = sub_comp.add_tasklet(
        "sub", {"a_in", "q", "r"}, {"a_out"}, "a_out = a_in - q * r"
    )
    sub_comp.add_memlet_path(
        sub_comp.add_read("A"), t_sub, dst_conn="a_in", memlet=Memlet("A[i_sub, j]")
    )
    sub_comp.add_memlet_path(
        sub_comp.add_read("Q"), t_sub, dst_conn="q", memlet=Memlet("Q[i_sub, k]")
    )
    sub_comp.add_memlet_path(
        sub_comp.add_read("R"), t_sub, dst_conn="r", memlet=Memlet("R[k, j]")
    )
    sub_comp.add_memlet_path(
        t_sub, sub_comp.add_write("A"), src_conn="a_out", memlet=Memlet("A[i_sub, j]")
    )

    final_state = sdfg.add_state("final")
    sdfg.add_edge(k_loop, final_state, InterstateEdge())

    return sdfg


def generate_adi_sdfg(name: str = "adi") -> SDFG:
    """
    Generates an SDFG for the ADI (Alternating Direction Implicit) stencil.
    Faithful implementation of tools/demo/npbench/adi.py.txt.
    """
    N = dace.symbol("N", dace.int64)
    TSTEPS = dace.symbol("TSTEPS", dace.int64)

    sdfg = SDFG(name)
    sdfg.add_array("u", [N, N], dace.float64)
    sdfg.add_array("v", [N, N], dace.float64)
    sdfg.add_array("p", [N, N], dace.float64)
    sdfg.add_array("q", [N, N], dace.float64)

    # Constants as symbols
    for c_name in ["a", "b", "c", "d", "e", "f"]:
        sdfg.add_symbol(c_name, dace.float64)

    init_state = sdfg.add_state("init", is_start_block=True)

    # Time loop t: 1 to TSTEPS+1
    time_loop = LoopRegion("time_loop", "t <= TSTEPS", "t", "t=1", "t=t+1")
    sdfg.add_node(time_loop)
    sdfg.add_edge(init_state, time_loop, InterstateEdge())

    # =========================================================================
    # PART 1: Column Sweep (Implicit X)
    # Solving for v using u
    # =========================================================================

    # 1. Initialization
    # v[0, 1:N-1] = 1.0
    # p[1:N-1, 0] = 0.0
    # q[1:N-1, 0] = v[0, 1:N-1]

    # We can do this in one LoopRegion over 'i' (1..N-1)
    col_init_loop = LoopRegion("col_init_loop", "i < N-1", "i", "i=1", "i=i+1")
    time_loop.add_node(col_init_loop, is_start_block=True)

    col_init_state = col_init_loop.add_state("col_init_state", is_start_block=True)

    # Shared AccessNode for v to enforce ordering (Write -> Read)
    v_access = col_init_state.add_access("v")

    # v[0, i] = 1.0
    t_v_init = col_init_state.add_tasklet("init_v", {}, {"o"}, "o = 1.0")
    col_init_state.add_memlet_path(
        t_v_init, v_access, src_conn="o", memlet=Memlet("v[0, i]")
    )

    # p[i, 0] = 0.0
    t_p_init = col_init_state.add_tasklet("init_p", {}, {"o"}, "o = 0.0")
    col_init_state.add_memlet_path(
        t_p_init, col_init_state.add_write("p"), src_conn="o", memlet=Memlet("p[i, 0]")
    )

    # q[i, 0] = v[0, i]
    # Connect from the same v_access node to ensure t_q_init runs after t_v_init
    t_q_init = col_init_state.add_tasklet("init_q", {"v_in"}, {"q_out"}, "q_out = v_in")
    col_init_state.add_memlet_path(
        v_access, t_q_init, dst_conn="v_in", memlet=Memlet("v[0, i]")
    )
    col_init_state.add_memlet_path(
        t_q_init,
        col_init_state.add_write("q"),
        src_conn="q_out",
        memlet=Memlet("q[i, 0]"),
    )

    # 2. Forward Sweep Loop (j=1..N-1)
    col_sweep_1 = LoopRegion("col_sweep_1", "j < N-1", "j", "j=1", "j=j+1")
    time_loop.add_node(col_sweep_1)
    time_loop.add_edge(col_init_loop, col_sweep_1, InterstateEdge())

    # Inner loop i (1..N-1)
    row_loop_1 = LoopRegion("row_loop_1", "i < N-1", "i", "i=1", "i=i+1")
    col_sweep_1.add_node(row_loop_1, is_start_block=True)

    comp_state_1 = row_loop_1.add_state("comp_1", is_start_block=True)

    # p[i, j] calculation
    t_p = comp_state_1.add_tasklet(
        "calc_p", {"p_prev"}, {"p_out"}, "p_out = -c / (a * p_prev + b)"
    )

    # q[i, j] calculation
    # q[i, j] = (-d * u[j, i-1] + (1.0 + 2.0 * d) * u[j, i] - f * u[j, i+1] - a * q[i, j-1]) / (a * p[i, j-1] + b)
    t_q = comp_state_1.add_tasklet(
        "calc_q",
        {"p_prev", "q_prev", "u_west", "u_center", "u_east"},
        {"q_out"},
        "q_out = (-d * u_west + (1.0 + 2.0 * d) * u_center - f * u_east - a * q_prev) / (a * p_prev + b)",
    )

    # Inputs for t_p
    comp_state_1.add_memlet_path(
        comp_state_1.add_read("p"), t_p, dst_conn="p_prev", memlet=Memlet("p[i, j-1]")
    )

    # Inputs for t_q
    comp_state_1.add_memlet_path(
        comp_state_1.add_read("p"), t_q, dst_conn="p_prev", memlet=Memlet("p[i, j-1]")
    )
    comp_state_1.add_memlet_path(
        comp_state_1.add_read("q"), t_q, dst_conn="q_prev", memlet=Memlet("q[i, j-1]")
    )
    comp_state_1.add_memlet_path(
        comp_state_1.add_read("u"), t_q, dst_conn="u_west", memlet=Memlet("u[j, i-1]")
    )
    comp_state_1.add_memlet_path(
        comp_state_1.add_read("u"), t_q, dst_conn="u_center", memlet=Memlet("u[j, i]")
    )
    comp_state_1.add_memlet_path(
        comp_state_1.add_read("u"), t_q, dst_conn="u_east", memlet=Memlet("u[j, i+1]")
    )

    # Outputs
    comp_state_1.add_memlet_path(
        t_p, comp_state_1.add_write("p"), src_conn="p_out", memlet=Memlet("p[i, j]")
    )
    comp_state_1.add_memlet_path(
        t_q, comp_state_1.add_write("q"), src_conn="q_out", memlet=Memlet("q[i, j]")
    )

    # 3. Post-Forward Initialization (v boundary)
    # v[N-1, 1:N-1] = 1.0
    v_bound_loop = LoopRegion("v_bound_loop", "i < N-1", "i", "i=1", "i=i+1")
    time_loop.add_node(v_bound_loop)
    time_loop.add_edge(col_sweep_1, v_bound_loop, InterstateEdge())

    v_bound_state = v_bound_loop.add_state("v_bound_state", is_start_block=True)
    t_v_bound = v_bound_state.add_tasklet("init_v_bound", {}, {"o"}, "o = 1.0")
    v_bound_state.add_memlet_path(
        t_v_bound,
        v_bound_state.add_write("v"),
        src_conn="o",
        memlet=Memlet("v[N-1, i]"),
    )

    # 4. Backward Sweep Loop (j=N-2..0)
    col_sweep_2 = LoopRegion("col_sweep_2", "j > 0", "j", "j=N-2", "j=j-1")
    time_loop.add_node(col_sweep_2)
    time_loop.add_edge(v_bound_loop, col_sweep_2, InterstateEdge())

    row_loop_2 = LoopRegion("row_loop_2", "i < N-1", "i", "i=1", "i=i+1")
    col_sweep_2.add_node(row_loop_2, is_start_block=True)

    comp_state_2 = row_loop_2.add_state("comp_2", is_start_block=True)

    # v[j, i] = p[i, j] * v[j+1, i] + q[i, j]
    t_v = comp_state_2.add_tasklet(
        "calc_v",
        {"p_val", "v_next", "q_val"},
        {"v_out"},
        "v_out = p_val * v_next + q_val",
    )

    comp_state_2.add_memlet_path(
        comp_state_2.add_read("p"), t_v, dst_conn="p_val", memlet=Memlet("p[i, j]")
    )
    comp_state_2.add_memlet_path(
        comp_state_2.add_read("v"), t_v, dst_conn="v_next", memlet=Memlet("v[j+1, i]")
    )
    comp_state_2.add_memlet_path(
        comp_state_2.add_read("q"), t_v, dst_conn="q_val", memlet=Memlet("q[i, j]")
    )
    comp_state_2.add_memlet_path(
        t_v, comp_state_2.add_write("v"), src_conn="v_out", memlet=Memlet("v[j, i]")
    )

    # =========================================================================
    # PART 2: Row Sweep (Implicit Y)
    # Solving for u using v
    # =========================================================================

    # 5. Initialization for Part 2
    # u[1:N-1, 0] = 1.0
    # p[1:N-1, 0] = 0.0
    # q[1:N-1, 0] = u[1:N-1, 0]

    row_init_loop = LoopRegion("row_init_loop", "i < N-1", "i", "i=1", "i=i+1")
    time_loop.add_node(row_init_loop)
    time_loop.add_edge(col_sweep_2, row_init_loop, InterstateEdge())

    row_init_state = row_init_loop.add_state("row_init_state", is_start_block=True)

    # Shared AccessNode for u to enforce ordering
    u_access = row_init_state.add_access("u")

    # u[i, 0] = 1.0
    t_u_init = row_init_state.add_tasklet("init_u", {}, {"o"}, "o = 1.0")
    row_init_state.add_memlet_path(
        t_u_init, u_access, src_conn="o", memlet=Memlet("u[i, 0]")
    )

    # p[i, 0] = 0.0
    t_p_init_2 = row_init_state.add_tasklet("init_p_2", {}, {"o"}, "o = 0.0")
    row_init_state.add_memlet_path(
        t_p_init_2,
        row_init_state.add_write("p"),
        src_conn="o",
        memlet=Memlet("p[i, 0]"),
    )

    # q[i, 0] = u[i, 0]
    t_q_init_2 = row_init_state.add_tasklet(
        "init_q_2", {"u_in"}, {"q_out"}, "q_out = u_in"
    )
    row_init_state.add_memlet_path(
        u_access, t_q_init_2, dst_conn="u_in", memlet=Memlet("u[i, 0]")
    )
    row_init_state.add_memlet_path(
        t_q_init_2,
        row_init_state.add_write("q"),
        src_conn="q_out",
        memlet=Memlet("q[i, 0]"),
    )

    # 6. Forward Sweep Loop (j=1..N-1)
    row_sweep_1 = LoopRegion("row_sweep_1", "j < N-1", "j", "j=1", "j=j+1")
    time_loop.add_node(row_sweep_1)
    time_loop.add_edge(row_init_loop, row_sweep_1, InterstateEdge())

    # Inner loop i (1..N-1)
    row_loop_3 = LoopRegion("row_loop_3", "i < N-1", "i", "i=1", "i=i+1")
    row_sweep_1.add_node(row_loop_3, is_start_block=True)

    comp_state_3 = row_loop_3.add_state("comp_3", is_start_block=True)

    # p[i, j] calculation: p[i, j] = -f / (d * p[i, j-1] + e)
    t_p_2 = comp_state_3.add_tasklet(
        "calc_p_2", {"p_prev"}, {"p_out"}, "p_out = -f / (d * p_prev + e)"
    )

    # q[i, j] calculation:
    # q[i, j] = (-a * v[i-1, j] + (1.0 + 2.0 * a) * v[i, j] - c * v[i+1, j] - d * q[i, j-1]) / (d * p[i, j-1] + e)
    t_q_2 = comp_state_3.add_tasklet(
        "calc_q_2",
        {"p_prev", "q_prev", "v_west", "v_center", "v_east"},
        {"q_out"},
        "q_out = (-a * v_west + (1.0 + 2.0 * a) * v_center - c * v_east - d * q_prev) / (d * p_prev + e)",
    )

    # Inputs for t_p_2
    comp_state_3.add_memlet_path(
        comp_state_3.add_read("p"), t_p_2, dst_conn="p_prev", memlet=Memlet("p[i, j-1]")
    )

    # Inputs for t_q_2
    comp_state_3.add_memlet_path(
        comp_state_3.add_read("p"), t_q_2, dst_conn="p_prev", memlet=Memlet("p[i, j-1]")
    )
    comp_state_3.add_memlet_path(
        comp_state_3.add_read("q"), t_q_2, dst_conn="q_prev", memlet=Memlet("q[i, j-1]")
    )
    comp_state_3.add_memlet_path(
        comp_state_3.add_read("v"), t_q_2, dst_conn="v_west", memlet=Memlet("v[i-1, j]")
    )
    comp_state_3.add_memlet_path(
        comp_state_3.add_read("v"), t_q_2, dst_conn="v_center", memlet=Memlet("v[i, j]")
    )
    comp_state_3.add_memlet_path(
        comp_state_3.add_read("v"), t_q_2, dst_conn="v_east", memlet=Memlet("v[i+1, j]")
    )

    # Outputs
    comp_state_3.add_memlet_path(
        t_p_2, comp_state_3.add_write("p"), src_conn="p_out", memlet=Memlet("p[i, j]")
    )
    comp_state_3.add_memlet_path(
        t_q_2, comp_state_3.add_write("q"), src_conn="q_out", memlet=Memlet("q[i, j]")
    )

    # 7. Post-Forward Initialization (u boundary)
    # u[1:N-1, N-1] = 1.0
    u_bound_loop = LoopRegion("u_bound_loop", "i < N-1", "i", "i=1", "i=i+1")
    time_loop.add_node(u_bound_loop)
    time_loop.add_edge(row_sweep_1, u_bound_loop, InterstateEdge())

    u_bound_state = u_bound_loop.add_state("u_bound_state", is_start_block=True)
    t_u_bound = u_bound_state.add_tasklet("init_u_bound", {}, {"o"}, "o = 1.0")
    u_bound_state.add_memlet_path(
        t_u_bound,
        u_bound_state.add_write("u"),
        src_conn="o",
        memlet=Memlet("u[i, N-1]"),
    )

    # 8. Backward Sweep Loop (j=N-2..0)
    row_sweep_2 = LoopRegion("row_sweep_2", "j > 0", "j", "j=N-2", "j=j-1")
    time_loop.add_node(row_sweep_2)
    time_loop.add_edge(u_bound_loop, row_sweep_2, InterstateEdge())

    row_loop_4 = LoopRegion("row_loop_4", "i < N-1", "i", "i=1", "i=i+1")
    row_sweep_2.add_node(row_loop_4, is_start_block=True)

    comp_state_4 = row_loop_4.add_state("comp_4", is_start_block=True)

    # u[i, j] = p[i, j] * u[i, j+1] + q[i, j]
    t_u = comp_state_4.add_tasklet(
        "calc_u",
        {"p_val", "u_next", "q_val"},
        {"u_out"},
        "u_out = p_val * u_next + q_val",
    )

    comp_state_4.add_memlet_path(
        comp_state_4.add_read("p"), t_u, dst_conn="p_val", memlet=Memlet("p[i, j]")
    )
    comp_state_4.add_memlet_path(
        comp_state_4.add_read("u"), t_u, dst_conn="u_next", memlet=Memlet("u[i, j+1]")
    )
    comp_state_4.add_memlet_path(
        comp_state_4.add_read("q"), t_u, dst_conn="q_val", memlet=Memlet("q[i, j]")
    )
    comp_state_4.add_memlet_path(
        t_u, comp_state_4.add_write("u"), src_conn="u_out", memlet=Memlet("u[i, j]")
    )

    final_state = sdfg.add_state("final")
    sdfg.add_edge(time_loop, final_state, InterstateEdge())

    return sdfg


def _process_sdfg(
    sdfg: SDFG, name: str, out_dir: str, description: str, suffix: str = ""
):
    """
    Helper function to save, validate, and print information about an SDFG.
    """
    filepath = os.path.join(out_dir, f"{name}{suffix}.sdfgz")
    print(f"{description} saved to {filepath}")
    sdfg.save(filepath, compress=True)
    sdfg.validate()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    # Default output directory relative to project root
    default_out_dir = os.path.join(project_root, "tools", "demo", "npbench-sdfg")
    parser.add_argument(
        "-d", "--out-dir", default=default_out_dir, help="Output directory"
    )
    args = parser.parse_args()

    os.makedirs(args.out_dir, exist_ok=True)

    # --- Heat3D ---
    print("Generating Heat3D SDFGs...")

    # Original Heat3D SDFG (LoopRegions)
    sdfg_heat3d_loop = generate_heat3d_sdfg()
    sdfg_heat3d_loop.simplify()
    expand_scalars(sdfg_heat3d_loop)
    _process_sdfg(
        sdfg_heat3d_loop, "heat3d", args.out_dir, "Heat3D original (LoopRegion)"
    )

    # Heat3D transformed to Maps
    sdfg_heat3d_map = deepcopy(sdfg_heat3d_loop)
    sdfg_heat3d_map.name = "heat3d_map"
    sdfg_heat3d_map.apply_transformations_repeated(LoopToMap)
    sdfg_heat3d_map.simplify()
    _process_sdfg(
        sdfg_heat3d_map,
        "heat3d",
        args.out_dir,
        "Heat3d transformed (LoopToMap)",
        "_map",
    )
    print("Heat3D done.")

    # --- SpMV ---
    print("\nGenerating SpMV SDFGs...")

    # Original SpMV SDFG (LoopRegion)
    sdfg_spmv_loop = generate_spmv_sdfg()
    sdfg_spmv_loop.simplify()
    # expand_scalars(sdfg_spmv_loop) # Keep original unexpanded
    _process_sdfg(sdfg_spmv_loop, "spmv", args.out_dir, "SpMV original (LoopRegion)")

    # SpMV Expanded
    sdfg_spmv_expanded = deepcopy(sdfg_spmv_loop)
    sdfg_spmv_expanded.name = "spmv_expanded"
    expand_scalars(sdfg_spmv_expanded)
    _process_sdfg(
        sdfg_spmv_expanded, "spmv", args.out_dir, "SpMV expanded", "_expanded"
    )

    # SpMV transformed (ScalarExpansion and LoopToMap)
    sdfg_spmv_map = deepcopy(sdfg_spmv_expanded)
    sdfg_spmv_map.name = "spmv_map"
    # To properly parallelize the outer loop, a ScalarExpansion pass would typically
    # be applied first to `accum`. Without it, LoopToMap will keep `accum` serial.
    sdfg_spmv_map.apply_transformations_repeated(LoopToMap)
    sdfg_spmv_map.simplify()
    _process_sdfg(
        sdfg_spmv_map, "spmv", args.out_dir, "SpMV transformed (LoopToMap)", "_map"
    )
    print("SpMV done.")

    # --- Gram-Schmidt ---
    print("\nGenerating Gram-Schmidt SDFGs...")

    # Original Gram-Schmidt SDFG (LoopRegion)
    sdfg_gs_loop = generate_gram_schmidt_sdfg()
    sdfg_gs_loop.simplify()
    # expand_scalars(sdfg_gs_loop) # Do it explicitly to test
    # We want to show 'nrm' being expanded
    _process_sdfg(
        sdfg_gs_loop, "gram_schmidt", args.out_dir, "Gram-Schmidt original (LoopRegion)"
    )

    # Apply expansion
    sdfg_gs_expanded = deepcopy(sdfg_gs_loop)
    sdfg_gs_expanded.name = "gram_schmidt_expanded"
    expand_scalars(sdfg_gs_expanded)
    _process_sdfg(
        sdfg_gs_expanded,
        "gram_schmidt",
        args.out_dir,
        "Gram-Schmidt expanded",
        "_expanded",
    )

    # Transformed to Maps
    sdfg_gs_map = deepcopy(sdfg_gs_expanded)
    sdfg_gs_map.name = "gram_schmidt_map"
    sdfg_gs_map.apply_transformations_repeated(LoopToMap)
    sdfg_gs_map.simplify()
    _process_sdfg(
        sdfg_gs_map,
        "gram_schmidt",
        args.out_dir,
        "Gram-Schmidt transformed (LoopToMap)",
        "_map",
    )
    print("Gram-Schmidt done.")

    # --- ADI ---
    print("\nGenerating ADI SDFGs...")

    # Original ADI SDFG (LoopRegion)
    sdfg_adi_loop = generate_adi_sdfg()
    sdfg_adi_loop.simplify()
    _process_sdfg(sdfg_adi_loop, "adi", args.out_dir, "ADI original (LoopRegion)")

    # ADI Expanded
    sdfg_adi_expanded = deepcopy(sdfg_adi_loop)
    sdfg_adi_expanded.name = "adi_expanded"
    expand_scalars(sdfg_adi_expanded)
    _process_sdfg(sdfg_adi_expanded, "adi", args.out_dir, "ADI expanded", "_expanded")

    # ADI transformed (LoopToMap)
    # The inner 'i' loops should be parallelized (mapped), while 'j' loops remain sequential.
    sdfg_adi_map = deepcopy(sdfg_adi_expanded)
    sdfg_adi_map.name = "adi_map"
    sdfg_adi_map.apply_transformations_repeated(LoopToMap)
    sdfg_adi_map.simplify()
    _process_sdfg(
        sdfg_adi_map, "adi", args.out_dir, "ADI transformed (LoopToMap)", "_map"
    )
    print("ADI done.")

    print("\nAll SDFGs generated and validated successfully.")
