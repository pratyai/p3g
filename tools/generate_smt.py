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
from tests.utils import solve_smt_string, TimeoutError
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
    negated_query = None  # Initialize negated_query for potential generation

    if query_type == "D-FS":
        smt_query = exists_data_exists_bounds_forall_iter_isdep(
            loop_node, verbose=False
        )
    elif query_type == "D-FS/B":
        # Generate both main and negated query for D-FS/B
        smt_query = exists_data_forall_bounds_forall_iters_chained(
            loop_node, verbose=False, build_negated=False
        )
        negated_query = exists_data_forall_bounds_forall_iters_chained(
            loop_node, verbose=False, build_negated=True
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

    if negated_query:
        negated_output_path = args.output.replace(".smt2", "_negated.smt2")
        with open(negated_output_path, "w") as f:
            f.write(negated_query)
        print(f"Negated SMT-LIB query generated and saved to {negated_output_path}")

    # --- Solving and Reporting ---
    print("\n--- Solving Primary Query ---")
    main_result_str = "UNKNOWN"
    try:
        main_result = solve_smt_string(smt_query, 120)
        main_is_sat = main_result.is_sat
        main_result_str = "SAT" if main_is_sat else "UNSAT"
        print(
            f"Primary Query Result: {main_result_str} (Time: {main_result.time_elapsed:.4f}s, "
            f"Quantifiers: {main_result.num_quantifiers}, Atoms: {main_result.num_atoms}, "
            f"And: {main_result.num_and}, Or: {main_result.num_or}, Size: {main_result.formula_size})"
        )
    except SolverReturnedUnknownResultError:
        print("Primary Query Result: UNKNOWN (Solver returned unknown)")
    except TimeoutError:
        print("Primary Query Result: UNKNOWN (Timeout)")
    except Exception as e:
        print(f"Primary Query Result: ERROR - {e}")

    if negated_query:
        print("\n--- Solving Negated Query ---")
        negated_result_str = "UNKNOWN"
        try:
            negated_result = solve_smt_string(negated_query, 120)
            negated_is_sat = negated_result.is_sat
            negated_result_str = "SAT" if negated_is_sat else "UNSAT"
            print(
                f"Negated Query Result: {negated_result_str} (Time: {negated_result.time_elapsed:.4f}s, "
                f"Quantifiers: {negated_result.num_quantifiers}, Atoms: {negated_result.num_atoms}, "
                f"And: {negated_result.num_and}, Or: {negated_result.num_or}, Size: {negated_result.formula_size})"
            )
        except SolverReturnedUnknownResultError:
            print("Negated Query Result: UNKNOWN (Solver returned unknown)")
        except TimeoutError:
            print("Negated Query Result: UNKNOWN (Timeout)")
        except Exception as e:
            print(f"Negated Query Result: ERROR - {e}")

        print("\n--- Interpretation ---")
        if main_result_str == "SAT" and negated_result_str == "UNSAT":
            print("Conclusion: The property (D-FS/B) holds. No counterexample found.")
        elif main_result_str == "UNSAT" and negated_result_str == "SAT":
            print(
                "Conclusion: The property (D-FS/B) does NOT hold. A counterexample (witness) was found."
            )
        elif main_result_str == "UNKNOWN" and negated_result_str == "SAT":
            print(
                "Conclusion: Primary query UNKNOWN, but negated query SAT. Interpreting primary as UNSAT."
            )
            print(
                "            The property (D-FS/B) does NOT hold. A counterexample (witness) was found."
            )
        elif main_result_str == "UNKNOWN" and negated_result_str == "UNSAT":
            print(
                "Conclusion: Primary query UNKNOWN, but negated query UNSAT. Interpreting primary as SAT."
            )
            print("            The property (D-FS/B) holds. No counterexample found.")
        elif main_result_str == "UNKNOWN" or negated_result_str == "UNKNOWN":
            print(
                "Conclusion: At least one query returned UNKNOWN. Cannot provide a definitive interpretation."
            )
        else:
            print(
                f"Conclusion: Results are inconclusive or indicate an issue with query generation/solver consistency."
            )
            print(
                f"            Primary: {main_result_str}, Negated: {negated_result_str}"
            )
    elif main_result_str == "UNKNOWN":
        print(
            f"Conclusion: Only primary query was run, and it returned UNKNOWN. Cannot provide a definitive interpretation."
        )


if __name__ == "__main__":
    main()
