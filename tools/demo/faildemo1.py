#!/usr/bin/env python3
import os
import numpy as np

import dace
from dace.sdfg import SDFG, InterstateEdge
from dace.sdfg.state import LoopRegion
from dace.transformation.interstate import LoopToMap


def generate_faildemo1_sdfg():
    sdfg = SDFG("faildemo1")

    # Symbols
    kidia = dace.symbol("kidia", dace.int32)
    kfdia = dace.symbol("kfdia", dace.int32)
    sdfg.add_symbol("kidia", dace.int32)
    sdfg.add_symbol("kfdia", dace.int32)

    # Array zqlhs
    # Dimensions:
    # Dim 0: spatial (kidia/kfdia range) -> let's assume size N large enough, e.g. 1000 or symbol K
    # Dim 1: inner loop iterator (1..4) -> size 5 to be safe
    # Dim 2: outer loop iterator (0..3) -> size 5 to be safe
    # Using generic "N" for dim 0.
    N = dace.symbol("N", dace.int32)
    sdfg.add_array("zqlhs", [N, 5, 5], dace.float64)

    # Init state
    init_state = sdfg.add_state("init", is_start_block=True)

    # Outer Loop (L1170): _for_it_99 = 0 to 3
    # Condition: _for_it_99 < 4 (since 3 is inclusive end)
    outer_loop = LoopRegion(
        "L1170",
        condition_expr="_for_it_99 < 4",
        loop_var="_for_it_99",
        initialize_expr="_for_it_99 = 0",
        update_expr="_for_it_99 = _for_it_99 + 1",
    )
    sdfg.add_node(outer_loop)
    sdfg.add_edge(init_state, outer_loop, InterstateEdge())

    # Inner Loop (L1171): _for_it_100 = (1 + _for_it_99) to 4
    # Condition: _for_it_100 < 5 (since 4 is inclusive end)
    inner_loop = LoopRegion(
        "L1171",
        condition_expr="_for_it_100 < 5",
        loop_var="_for_it_100",
        initialize_expr="_for_it_100 = _for_it_99 + 1",
        update_expr="_for_it_100 = _for_it_100 + 1",
    )
    outer_loop.add_node(inner_loop, is_start_block=True)

    # Inside inner loop: Map (M1172)
    # Range: kidia-1 to kfdia-1 (inclusive)
    # DaCe Map range is usually start:stop (exclusive). So start=kidia-1, stop=kfdia.
    map_state = inner_loop.add_state("M1172_state", is_start_block=True)

    # Reads: zqlhs[tmp, _for_it_100, _for_it_99], zqlhs[tmp, _for_it_99, _for_it_99]
    # Writes: zqlhs[tmp, _for_it_100, _for_it_99]

    # Access Nodes
    r_zqlhs = map_state.add_read("zqlhs")
    w_zqlhs = map_state.add_write("zqlhs")

    # Map Entry/Exit
    # tmp_parfor_52
    me, mx = map_state.add_map("M1172", {"tmp_parfor_52": "kidia-1 : kfdia"})

    # Tasklet T1174
    tasklet = map_state.add_tasklet(
        "T1174",
        {"in_a", "in_b"},
        {"out"},
        "out = in_a + in_b",  # Addition operation
    )

    # Memlets
    # Input 1: zqlhs[tmp_parfor_52, _for_it_100, _for_it_99]
    map_state.add_memlet_path(
        r_zqlhs,
        me,
        tasklet,
        dst_conn="in_a",
        memlet=dace.Memlet("zqlhs[tmp_parfor_52, _for_it_100, _for_it_99]"),
    )

    # Input 2: zqlhs[tmp_parfor_52, _for_it_99, _for_it_99]
    map_state.add_memlet_path(
        r_zqlhs,
        me,
        tasklet,
        dst_conn="in_b",
        memlet=dace.Memlet("zqlhs[tmp_parfor_52, _for_it_99, _for_it_99]"),
    )

    # Output: zqlhs[tmp_parfor_52, _for_it_100, _for_it_99]
    map_state.add_memlet_path(
        tasklet,
        mx,
        w_zqlhs,
        src_conn="out",
        memlet=dace.Memlet("zqlhs[tmp_parfor_52, _for_it_100, _for_it_99]"),
    )

    # Final state (optional, LoopRegion handles exit)

    return sdfg


def generate_fully_parallel_sdfg():
    sdfg = SDFG("faildemo1_full_parallel")

    # Symbols
    kidia = dace.symbol("kidia", dace.int32)
    kfdia = dace.symbol("kfdia", dace.int32)
    sdfg.add_symbol("kidia", dace.int32)
    sdfg.add_symbol("kfdia", dace.int32)

    # Array zqlhs
    # Dimensions: [N, 5, 5]
    N = dace.symbol("N", dace.int32)
    sdfg.add_array("zqlhs", [N, 5, 5], dace.float64)

    # State
    state = sdfg.add_state("compute", is_start_block=True)

    # Access nodes
    r_zqlhs = state.add_read("zqlhs")
    w_zqlhs = state.add_write("zqlhs")

    # Outer Map (L1170): _for_it_99 = 0 to 3
    me_99, mx_99 = state.add_map("L1170_map", {"_for_it_99": "0:4"})

    # Inner Map (L1171): _for_it_100 = (_for_it_99 + 1) to 4
    # Range is inclusive start, exclusive end. Python range(start, 5) -> start..4.
    me_100, mx_100 = state.add_map("L1171_map", {"_for_it_100": "_for_it_99 + 1 : 5"})

    # Innermost Map (M1172): tmp_parfor_52
    me_52, mx_52 = state.add_map("M1172_map", {"tmp_parfor_52": "kidia-1 : kfdia"})

    # Tasklet
    tasklet = state.add_tasklet("T1174", {"in_a", "in_b"}, {"out"}, "out = in_a + in_b")

    # Connections
    # Read -> ME_99
    state.add_memlet_path(
        r_zqlhs,
        me_99,
        me_100,
        me_52,
        tasklet,
        dst_conn="in_a",
        memlet=dace.Memlet("zqlhs[tmp_parfor_52, _for_it_100, _for_it_99]"),
    )

    state.add_memlet_path(
        r_zqlhs,
        me_99,
        me_100,
        me_52,
        tasklet,
        dst_conn="in_b",
        memlet=dace.Memlet("zqlhs[tmp_parfor_52, _for_it_99, _for_it_99]"),
    )

    # Tasklet -> MX_52 -> ... -> Write
    state.add_memlet_path(
        tasklet,
        mx_52,
        mx_100,
        mx_99,
        w_zqlhs,
        src_conn="out",
        memlet=dace.Memlet("zqlhs[tmp_parfor_52, _for_it_100, _for_it_99]"),
    )

    return sdfg


if __name__ == "__main__":
    sdfg = generate_faildemo1_sdfg()

    # Validate
    sdfg.validate()

    # Determine project root and output paths
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_root = os.path.abspath(os.path.join(script_dir, os.pardir, os.pardir))
    output_dir = os.path.join(project_root, "tmp")
    os.makedirs(output_dir, exist_ok=True)

    output_path = os.path.join(output_dir, "faildemo1.sdfgz")
    sdfg.save(output_path, compress=True)
    print(f"SDFG saved to {output_path}")

    # --- Verification Setup ---
    print("\nVerifying...")
    kidia_val = 1
    kfdia_val = 5
    N_val = 20

    # Initial Data
    zqlhs_in = np.random.rand(N_val, 5, 5).astype(np.float64)

    # Compute Reference
    print("Computing reference...")
    ref_zqlhs = zqlhs_in.copy()
    for i99 in range(0, 4):
        for i100 in range(i99 + 1, 5):
            for tmp in range(kidia_val - 1, kfdia_val):
                ref_zqlhs[tmp, i100, i99] = (
                    ref_zqlhs[tmp, i100, i99] + ref_zqlhs[tmp, i99, i99]
                )

    # --- Test Initial SDFG ---
    print("Running initial SDFG...")
    zqlhs_out_initial = zqlhs_in.copy()
    sdfg(zqlhs=zqlhs_out_initial, kidia=kidia_val, kfdia=kfdia_val, N=N_val)

    if np.allclose(zqlhs_out_initial, ref_zqlhs):
        print("Initial SDFG Verification: PASSED")
    else:
        print("Initial SDFG Verification: FAILED")
        diff = np.abs(zqlhs_out_initial - ref_zqlhs)
        print(f"Max difference: {np.max(diff)}")
        exit(1)

    # --- Test Transformed SDFG ---
    print("\nApplying LoopToMap...")
    sdfg.apply_transformations_repeated(LoopToMap)
    output_path_map = os.path.join(output_dir, "faildemo1_map.sdfgz")
    sdfg.save(output_path_map, compress=True)
    print(f"SDFG MAP saved to {output_path_map}")
    sdfg.validate()

    print("Running transformed SDFG...")
    zqlhs_out_map = zqlhs_in.copy()
    sdfg(zqlhs=zqlhs_out_map, kidia=kidia_val, kfdia=kfdia_val, N=N_val)

    if np.allclose(zqlhs_out_map, ref_zqlhs):
        print("Transformed SDFG Verification: PASSED")
    else:
        print("Transformed SDFG Verification: FAILED")
        diff = np.abs(zqlhs_out_map - ref_zqlhs)
        print(f"Max difference: {np.max(diff)}")
        exit(1)

    # --- Test Fully Parallel SDFG ---
    print("\nGenerating and testing Fully Parallel SDFG...")
    sdfg_full = generate_fully_parallel_sdfg()
    output_path_full = os.path.join(output_dir, "faildemo1_fully_parallel.sdfgz")
    sdfg_full.save(output_path_full, compress=True)
    print(f"SDFG Full Parallel saved to {output_path_full}")
    sdfg_full.validate()
    sdfg_full.compile()

    print("Running Fully Parallel SDFG...")
    zqlhs_out_full = zqlhs_in.copy()
    sdfg_full(zqlhs=zqlhs_out_full, kidia=kidia_val, kfdia=kfdia_val, N=N_val)

    if np.allclose(zqlhs_out_full, ref_zqlhs):
        print("Fully Parallel SDFG Verification: PASSED")
    else:
        print("Fully Parallel SDFG Verification: FAILED")
        diff = np.abs(zqlhs_out_full - ref_zqlhs)
        print(f"Max difference: {np.max(diff)}")
        exit(1)
