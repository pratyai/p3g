import os
import sys

# Add the project root to the sys.path
script_dir = os.path.dirname(__file__)
project_root = os.path.abspath(os.path.join(script_dir, os.pardir))
sys.path.insert(0, project_root)

import argparse
import pathlib

from p3g.p3g import Loop
from p3g.parser import PseudocodeParser
from p3g.smt import (
    exists_data_exists_bounds_forall_iter_isdep,
    exists_data_forall_bounds_forall_iter_isdep,
    exists_data_exists_bounds_exists_iter_isdep,
    exists_data_exists_bounds_forall_iter_isindep,
    exists_data_forall_bounds_forall_iter_isindep,
    forall_data_forall_bounds_forall_iter_isindep,
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
        help="Output file to write the generated SMT-LIB query. Defaults to <project_root>/tmp/<input_filename_without_extension>.smt2",
    )
    parser.add_argument(
        "-q",
        "--query-type",
        default="D-FS/DB",
        choices=["D-FS", "D-FS/B", "D-FS/DB", "I-FI", "I-FI/B", "I-FI/DB", "?"],
        help="""Type of SMT query to generate:
- D-FS: Does there exist a data configuration and a loop bound for which every adjacent iteration is dependent?
- D-FS/B: Does there exist a data configuration for which every adjacent iteration is dependent, for all loop bounds?
- D-NFI: Does there exist any data, any loop bounds, and any iteration pair for which a dependency exists?
- I-FI: Does there exist a data configuration and a loop bound for which all iteration pairs are independent?
- I-FI/B: Does there exist a data configuration for which all iteration pairs are independent, for all loop bounds?
- I-FI/DB: For all data configurations and all loop bounds, are all iteration pairs independent?""",
    )
    args = parser.parse_args()

    query_type = args.query_type
    if query_type == "?":
        import questionary

        # Map descriptive text to short query type names
        query_map = {
            "D-FS: Does there exist a data configuration and a loop bound for which every adjacent iteration is dependent?": "D-FS",
            "D-FS/B: Does there exist a data configuration for which every adjacent iteration is dependent, for all loop bounds?": "D-FS/B",
            "D-NFI: Does there exist any data, any loop bounds, and any iteration pair for which a dependency exists?": "D-NFI",
            "I-FI: Does there exist a data configuration and a loop bound for which all iteration pairs are independent?": "I-FI",
            "I-FI/B: Does there exist a data configuration for which all iteration pairs are independent, for all loop bounds?": "I-FI/B",
            "I-FI/DB: For all data configurations and all loop bounds, are all iteration pairs independent?": "I-FI/DB",
        }

        selected_description = questionary.select(
            "Select the type of SMT query to generate:",
            choices=list(query_map.keys()),
        ).ask()

        if selected_description is None:
            print("No query type selected. Exiting.")
            sys.exit(1)

        query_type = query_map[selected_description]

    # Determine output path if not provided
    if args.output is None:
        input_path = pathlib.Path(args.input)
        output_dir = pathlib.Path(project_root) / "tmp"
        output_dir.mkdir(parents=True, exist_ok=True)  # Ensure tmp directory exists
        args.output = str(output_dir / f"{input_path.stem}.smt2")

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
    if query_type == "D-FS":
        smt_query = exists_data_exists_bounds_exists_iter_isdep(
            loop_node, verbose=False
        )
    elif query_type == "D-FS/B":
        smt_query = exists_data_exists_bounds_forall_iter_isdep(
            loop_node, verbose=False
        )
    elif query_type == "D-FS/DB":
        smt_query = exists_data_forall_bounds_forall_iter_isdep(
            loop_node, verbose=False
        )
    elif query_type == "I-FI":
        smt_query = exists_data_exists_bounds_forall_iter_isindep(
            loop_node, verbose=False
        )
    elif query_type == "I-FI/B":
        smt_query = exists_data_forall_bounds_forall_iter_isindep(
            loop_node, verbose=False
        )
    elif query_type == "I-FI/DB":
        smt_query = forall_data_forall_bounds_forall_iter_isindep(
            loop_node, verbose=False
        )

    print(f"Generating SMT query of type: {query_type}")

    # Write SMT query to output file
    with open(args.output, "w") as f:
        f.write(smt_query)

    print(f"SMT-LIB query generated and saved to {args.output}")


if __name__ == "__main__":
    main()
