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
    expand_scalars(sdfg_spmv_loop)
    _process_sdfg(sdfg_spmv_loop, "spmv", args.out_dir, "SpMV original (LoopRegion)")

    # SpMV transformed (ScalarExpansion and LoopToMap)
    sdfg_spmv_map = deepcopy(sdfg_spmv_loop)
    sdfg_spmv_map.name = "spmv_map"
    # To properly parallelize the outer loop, a ScalarExpansion pass would typically
    # be applied first to `accum`. Without it, LoopToMap will keep `accum` serial.
    sdfg_spmv_map.apply_transformations_repeated(LoopToMap)
    sdfg_spmv_map.simplify()
    _process_sdfg(
        sdfg_spmv_map, "spmv", args.out_dir, "SpMV transformed (LoopToMap)", "_map"
    )
    print("SpMV done.")

    print("\nAll SDFGs generated and validated successfully.")
