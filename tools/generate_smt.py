import os
import sys

# Add the project root to the sys.path
script_dir = os.path.dirname(__file__)
project_root = os.path.abspath(os.path.join(script_dir, os.pardir))
sys.path.insert(0, project_root)

import argparse

from p3g.p3g import Loop
from p3g.parser import PseudocodeParser
from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
    generate_smt_for_prove_exists_data_forall_iter_isindep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
)


def main():
    parser = argparse.ArgumentParser(
        description="Generate SMT-LIB query from pseudocode."
    )
    parser.add_argument(
        "-i", "--input", required=True, help="Input file containing pseudocode."
    )
    parser.add_argument(
        "-o",
        "--output",
        required=True,
        help="Output file to write the generated SMT-LIB query.",
    )
    parser.add_argument(
        "-q",
        "--query-type",
        default="exists_data_forall_bounds_forall_its",
        choices=[
            "exists_data_forall_iter_isdep",
            "exists_data_forall_bounds_forall_its",
            "exists_data_exists_bounds_exists_iter_isdep",
            "exists_data_forall_iter_isindep",
            "exists_data_forall_bounds_forall_iter_isindep",
            "forall_data_forall_bounds_forall_iter_isindep",
        ],
        help="Type of SMT query to generate.",
    )
    args = parser.parse_args()

    # Read pseudocode from input file
    with open(args.input, "r") as f:
        pseudocode = f.read()

    # Parse pseudocode to P3G graph
    parser = PseudocodeParser()
    root_graph = parser.parse(pseudocode)

    # Find the top-level loop node in the graph
    loop_node = None
    for node in root_graph.nodes:
        if isinstance(node, Loop):
            loop_node = node
            break

    if loop_node is None:
        print("Error: Input pseudocode must define a top-level loop.")
        exit(1)

    # Generate SMT query based on selected type
    smt_query = ""
    if args.query_type == "exists_data_forall_iter_isdep":
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
    elif args.query_type == "exists_data_forall_bounds_forall_its":
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
    elif args.query_type == "exists_data_exists_bounds_exists_iter_isdep":
        smt_query = (
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep(
                loop_node, verbose=False
            )
        )
    elif args.query_type == "exists_data_forall_iter_isindep":
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isindep(
            loop_node, verbose=False
        )
    elif args.query_type == "exists_data_forall_bounds_forall_iter_isindep":
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep(
            loop_node, verbose=False
        )
    elif args.query_type == "forall_data_forall_bounds_forall_iter_isindep":
        smt_query = generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep(
            loop_node, verbose=False
        )

    # Write SMT query to output file
    with open(args.output, "w") as f:
        f.write(smt_query)

    print(f"SMT-LIB query generated and saved to {args.output}")


if __name__ == "__main__":
    main()
