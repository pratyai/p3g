import os
import sys

# Add the project root to the sys.path
script_dir = os.path.dirname(__file__)
project_root = os.path.abspath(os.path.join(script_dir, os.pardir))
sys.path.insert(0, project_root)

import argparse
import pathlib

from p3g.parser import PseudocodeParser
from p3g.smt import (
    exists_data_exists_bounds_forall_iter_isdep,
    exists_data_exists_bounds_exists_iter_isdep,
    exists_data_exists_bounds_forall_iter_isindep,
    exists_data_forall_bounds_forall_iter_isindep,
    forall_data_forall_bounds_forall_iter_isindep,
)
from p3g.smt_v2 import exists_data_forall_bounds_forall_iters_chained
from pysmt.exceptions import SolverReturnedUnknownResultError
from tests.utils import solve_smt_string
from p3g.graph import Branch, Map, Loop, Graph


def find_all_loop_nodes(graph: Graph) -> list[Loop]:
    """
    Recursively finds all Loop nodes within a graph and its nested structures.
    """
    found_loops = []
    for node in graph.nodes:
        if isinstance(node, Loop):
            found_loops.append(node)
            # Recursively search in the nested graph of this Loop
            found_loops.extend(find_all_loop_nodes(node.nested_graph))
        elif isinstance(node, Map):
            # Recursively search in the nested graph of this Map
            found_loops.extend(find_all_loop_nodes(node.nested_graph))
        elif isinstance(node, Branch):
            # Recursively search in all branch paths of this Branch
            for _, nested_graph in node.branches:
                found_loops.extend(find_all_loop_nodes(nested_graph))
    return found_loops


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
        choices=["D-FS", "D-FS/B", "D-NFI", "I-FI", "I-FI/B", "I-FI/DB", "?"],
        help="""Type of SMT query to generate:
- D-FS: Does there exist a data configuration and a loop bound for which every adjacent iteration is dependent?
- D-FS/B: Does there exist a data configuration for which every adjacent iteration is dependent, for all loop bounds?
- D-NFI: Does there exist any data, any loop bounds, and any iteration pair for which a dependency exists?
- I-FI: Does there exist a data configuration and a loop bound for which all iteration pairs are independent?
- I-FI/B: Does there exist a data configuration for which all iteration pairs are independent, for all loop bounds?
- I-FI/DB: For all data configurations and all loop bounds, are all iteration pairs independent?""",
    )
    parser.add_argument(
        "-l",
        "--loop-index",
        default="?",
        help="""Specify the 0-based index of the loop to analyze, or '?' to interactively select from a list of loops found in the pseudocode.
The interactive selection will display a summary of each loop (variable and bounds).
Defaults to '?'.""",
    )
    args = parser.parse_args()

    # Handle directory input
    if os.path.isdir(args.input):
        import questionary

        pcode_files = list(pathlib.Path(args.input).rglob("*.pcode"))

        if not pcode_files:
            print(f"Error: No .pcode files found in '{args.input}'.")
            sys.exit(1)

        # Create a list of string paths for the choices
        choices = [str(f) for f in pcode_files]

        selected_file = questionary.select(
            "Multiple .pcode files found. Please choose one:",
            choices=sorted(choices),
        ).ask()

        if selected_file is None:
            print("No file selected. Exiting.")
            sys.exit(1)

        args.input = selected_file

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

    # Collect all loop nodes in the graph hierarchy
    loop_nodes = find_all_loop_nodes(root_graph)

    # Implement loop selection logic
    selected_loop_node = None
    if args.loop_index == "?":
        import questionary

        if len(loop_nodes) == 1:
            selected_loop_node = loop_nodes[0]
            print("Only one loop found. Automatically selected it.")
        else:
            choices = []
            for i, loop in enumerate(loop_nodes):
                # Assuming Loop object has properties like .iterator_var, .lower_bound, .upper_bound
                # Adjust this formatting if Loop object has different attributes
                summary = (
                    f"Loop {i}: var={loop.loop_var}, bounds=[{loop.start}, {loop.end}]"
                )
                choices.append(summary)

            selected_description = questionary.select(
                "Select the loop to analyze:",
                choices=choices,
            ).ask()

            if selected_description is None:
                print("No loop selected. Exiting.")
                sys.exit(1)

            # Extract the index from the selected description (e.g., "Loop 0: ...")
            selected_index = int(selected_description.split(":")[0].split(" ")[1])
            selected_loop_node = loop_nodes[selected_index]
    else:
        try:
            loop_idx = int(args.loop_index)
            if 0 <= loop_idx < len(loop_nodes):
                selected_loop_node = loop_nodes[loop_idx]
            else:
                print(
                    f"Error: Loop index {loop_idx} is out of bounds. Found {len(loop_nodes)} loops."
                )
                sys.exit(1)
        except ValueError:
            print(
                f"Error: Invalid loop index '{args.loop_index}'. Must be a number or '?'."
            )
            sys.exit(1)

    # Assign the selected loop node to loop_node for subsequent use
    loop_node = selected_loop_node

    # Generate SMT query based on selected type
    smt_query = ""
    if query_type == "D-FS":
        smt_query = exists_data_exists_bounds_forall_iter_isdep(
            loop_node, verbose=False
        )
    elif query_type == "D-FS/B":
        smt_query = exists_data_forall_bounds_forall_iters_chained(
            loop_node, verbose=False, build_negated=False
        )
    elif query_type == "D-NFI":
        smt_query = exists_data_exists_bounds_exists_iter_isdep(
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
    else:
        raise ValueError(f"Unknown query type: {query_type}")

    print(f"Generating SMT query of type: {query_type}")

    # Write SMT query to output file
    with open(args.output, "w") as f:
        f.write(smt_query)

    print(f"SMT-LIB query generated and saved to {args.output}")

    try:
        main_is_sat = solve_smt_string(smt_query)
        # This part handles the case where the main query is UNSAT for D-FS/B
        if query_type == "D-FS/B" and not main_is_sat:
            print(
                "\nRegular query returned UNSAT. Trying negated query to find a witness..."
            )
            negated_query = exists_data_forall_bounds_forall_iters_chained(
                loop_node, verbose=False, build_negated=True
            )
            negated_output_path = args.output.replace(".smt2", "_negated.smt2")
            with open(negated_output_path, "w") as f:
                f.write(negated_query)
            print(f"Negated SMT-LIB query generated and saved to {negated_output_path}")

            try:
                # solve_smt_string will print the model if SAT
                negated_is_sat = solve_smt_string(negated_query)
                print("\n---")
                print(f"Regular query result: UNSAT")
                print(
                    f"Negated query result: {'SAT (witness found)' if negated_is_sat else 'UNSAT (no witness)'}"
                )
                print("---")
            except SolverReturnedUnknownResultError:
                print("\nNegated query returned UNKNOWN. Cannot provide a witness.")
            except Exception as e:
                print(
                    f"\nAn error occurred while solving the negated query for witness: {e}"
                )

    except SolverReturnedUnknownResultError:
        # This existing fallback logic handles cases where the main query returns UNKNOWN
        # We re-generate the negated query here.
        if query_type == "D-FS/B":
            print("\nRegular query returned UNKNOWN. Trying negated query...")
            negated_query = exists_data_forall_bounds_forall_iters_chained(
                loop_node, verbose=False, build_negated=True
            )
            negated_output_path = args.output.replace(".smt2", "_negated.smt2")
            with open(negated_output_path, "w") as f:
                f.write(negated_query)
            print(f"Negated SMT-LIB query generated and saved to {negated_output_path}")

            try:
                negated_is_sat = solve_smt_string(negated_query)
                print("\n---")
                print(f"Regular query result: UNKNOWN")
                print(f"Negated query result: {'SAT' if negated_is_sat else 'UNSAT'}")
                if negated_is_sat:
                    print(f"Interpreted result from negated query: UNSAT")
                else:
                    print(f"Interpreted result from negated query: SAT")
                print("---")

            except SolverReturnedUnknownResultError:
                print("\nNegated query also returned UNKNOWN. Final result is UNKNOWN.")
            except Exception as e:
                print(f"\nAn error occurred while solving the negated query: {e}")
        else:
            # If a non D-FS/B query returned unknown, re-raise it or print
            print(f"\nQuery type {query_type} returned UNKNOWN. No negated fallback.")
            raise  # Re-raise the original exception if no specific fallback


if __name__ == "__main__":
    main()
