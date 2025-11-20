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
        help="Output file to write the generated SMT-LIB query. Defaults to <project_root>/tmp/<input_filename_without_extension>.smt2",
    )
    parser.add_argument(
        "-q",
        "--query-type",
        default="D-FS/B",
        choices=["D-FS", "D-FS/B", "D-EX", "I-FI", "I-FI/B", "I-FI/AB", "?"],
        help="""Type of SMT query to generate:
- D-FS: Prove DOFS (Data-Oblivious Full Sequentiality). Finds if there exists a data configuration that makes all adjacent iterations dependent.
- D-FS/B: Same as D-FS, but also quantifies over symbolic loop bounds.
- D-EX: Prove Existence of any dependency. Finds if there exists any data, bounds, and iteration pair (j, k) with a dependency.
- I-FI: Prove DOFI (Data-Oblivious Full Independence). Finds if there exists a data configuration that makes all iterations independent.
- I-FI/B: Same as I-FI, but also quantifies over symbolic loop bounds.
- I-FI/AB: Same as I-FI, but quantifies over both symbolic data and loop bounds.""",
    )
    args = parser.parse_args()

    query_type = args.query_type
    if query_type == "?":
        import questionary

        # Map descriptive text to short query type names
        query_map = {
            "D-FS: Prove DOFS (Data-Oblivious Full Sequentiality).": "D-FS",
            "D-FS/B: DOFS with forall Bounds.": "D-FS/B",
            "D-EX: Prove Existence of any dependency.": "D-EX",
            "I-FI: Prove DOFI (Data-Oblivious Full Independence).": "I-FI",
            "I-FI/B: DOFI with forall Bounds.": "I-FI/B",
            "I-FI/AB: DOFI with forall Data and Bounds.": "I-FI/AB",
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
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop_node, verbose=False
        )
    elif query_type == "D-FS/B":
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
            loop_node, verbose=False
        )
    elif query_type == "D-EX":
        smt_query = (
            generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep(
                loop_node, verbose=False
            )
        )
    elif query_type == "I-FI":
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isindep(
            loop_node, verbose=False
        )
    elif query_type == "I-FI/B":
        smt_query = generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep(
            loop_node, verbose=False
        )
    elif query_type == "I-FI/AB":
        smt_query = generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep(
            loop_node, verbose=False
        )

    print(f"Generating SMT query of type: {query_type}")

    # Write SMT query to output file
    with open(args.output, "w") as f:
        f.write(smt_query)

    print(f"SMT-LIB query generated and saved to {args.output}")


if __name__ == "__main__":
    main()
