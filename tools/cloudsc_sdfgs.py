#!/usr/bin/env python3
import argparse
import os
import sys
from copy import deepcopy
import dace
from dace.sdfg import SDFG
from dace.transformation.interstate import LoopToMap
from dace.transformation.passes import find_promotable_scalars, ScalarToSymbolPromotion

# Ensure we can run this script from anywhere within the project
script_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(script_dir, os.pardir))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

from tools.array_ssa import expand_scalars


def _process_sdfg(sdfg, name, out_dir, description, suffix=""):
    filepath = os.path.join(out_dir, f"{name}{suffix}.sdfgz")
    print(f"{description} saved to {filepath}")
    sdfg.save(filepath, compress=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    # Default input: tools/demo/cloudsc_stage0.sdfgz
    default_input = os.path.join(project_root, "tools", "demo", "cloudsc_stage0.sdfgz")
    # Default output: tools/demo/cloudsc-sdfg
    default_out_dir = os.path.join(project_root, "tools", "demo", "cloudsc-sdfg")

    parser.add_argument("-i", "--input", default=default_input, help="Input SDFG path")
    parser.add_argument(
        "-d", "--out-dir", default=default_out_dir, help="Output directory"
    )
    args = parser.parse_args()

    os.makedirs(args.out_dir, exist_ok=True)

    if not os.path.exists(args.input):
        print(f"Error: Input file {args.input} not found.")
        sys.exit(1)

    print(f"Loading {args.input}...")
    sdfg_initial = SDFG.from_file(args.input)
    sdfg_initial.name = "cloudsc"

    # 1. Initial
    brrr = find_promotable_scalars(sdfg_initial, transients_only=False)
    print(brrr)
    huck = ScalarToSymbolPromotion()
    huck.transients_only = False
    huck.apply_pass(sdfg_initial, {})
    _process_sdfg(sdfg_initial, "cloudsc", args.out_dir, "CloudSC Initial")

    # 2. Initial Map (LoopToMap on initial)
    print("Generating Initial Map...")
    sdfg_initial_map = deepcopy(sdfg_initial)
    sdfg_initial_map.name = "cloudsc_initial_map"
    sdfg_initial_map.apply_transformations_repeated(LoopToMap)
    _process_sdfg(
        sdfg_initial_map, "cloudsc", args.out_dir, "CloudSC Initial Map", "_initial_map"
    )

    # 3. Expanded (Array SSA on initial)
    print("Generating Expanded...")
    sdfg_expanded = deepcopy(sdfg_initial)
    sdfg_expanded.name = "cloudsc_expanded"
    expand_scalars(sdfg_expanded)
    _process_sdfg(
        sdfg_expanded, "cloudsc", args.out_dir, "CloudSC Expanded", "_expanded"
    )

    # 4. Expanded Map (LoopToMap on expanded)
    print("Generating Expanded Map...")
    sdfg_map = deepcopy(sdfg_expanded)
    sdfg_map.name = "cloudsc_map"
    sdfg_map.apply_transformations_repeated(LoopToMap)
    _process_sdfg(
        sdfg_map, "cloudsc", args.out_dir, "CloudSC Map (from Expanded)", "_map"
    )

    print("Done.")
