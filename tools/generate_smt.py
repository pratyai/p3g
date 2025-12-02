import os
import sys
import sqlite3
import json

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


def log_to_db(db_path, data):
    """
    Logs the run details to a SQLite database.
    """
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()

    cursor.execute("""
        CREATE TABLE IF NOT EXISTS runs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
            input_file TEXT,
            loop_index INTEGER,
            query_type TEXT,
            main_result TEXT,
            main_time REAL,
            main_quantifiers INTEGER,
            main_atoms INTEGER,
            main_size INTEGER,
            main_variables INTEGER,
            main_arrays INTEGER,
            negated_result TEXT,
            negated_time REAL,
            negated_quantifiers INTEGER,
            negated_atoms INTEGER,
            negated_size INTEGER,
            negated_variables INTEGER,
            negated_arrays INTEGER,
            conclusion TEXT
        )
    """)

    cursor.execute(
        """
        INSERT INTO runs (
            input_file, loop_index, query_type,
            main_result, main_time, main_quantifiers, main_atoms, main_size, main_variables, main_arrays,
            negated_result, negated_time, negated_quantifiers, negated_atoms, negated_size, negated_variables, negated_arrays,
            conclusion
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """,
        (
            data.get("input_file"),
            data.get("loop_index"),
            data.get("query_type"),
            data.get("main_result"),
            data.get("main_time"),
            data.get("main_quantifiers"),
            data.get("main_atoms"),
            data.get("main_size"),
            data.get("main_variables"),
            data.get("main_arrays"),
            data.get("negated_result"),
            data.get("negated_time"),
            data.get("negated_quantifiers"),
            data.get("negated_atoms"),
            data.get("negated_size"),
            data.get("negated_variables"),
            data.get("negated_arrays"),
            data.get("conclusion"),
        ),
    )

    conn.commit()
    conn.close()


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
        "-db",
        "--db",
        help="Optional SQLite database file to log run details.",
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
    parser.add_argument(
        "-t",
        "--timeout",
        type=int,
        default=30,
        help="Solver timeout in seconds. Defaults to 30.",
    )
    args = parser.parse_args()

    # Handle directory input
    if os.path.isdir(args.input):
        import questionary

        pcode_files = list(pathlib.Path(args.input).glob("*.pcode"))

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
    final_loop_index = 0
    if args.loop_index == "?":
        import questionary

        if len(loop_nodes) == 1:
            selected_loop_node = loop_nodes[0]
            final_loop_index = 0
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
            final_loop_index = selected_index
    else:
        try:
            loop_idx = int(args.loop_index)
            if 0 <= loop_idx < len(loop_nodes):
                selected_loop_node = loop_nodes[loop_idx]
                final_loop_index = loop_idx
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

    # Determine output path if not provided
    if args.output is None:
        input_path = pathlib.Path(args.input)
        output_dir = pathlib.Path(project_root) / "tmp"
        output_dir.mkdir(parents=True, exist_ok=True)  # Ensure tmp directory exists
        args.output = str(output_dir / f"{input_path.stem}_l{final_loop_index}.smt2")

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

    # Prepare data for DB logging
    run_data = {
        "input_file": str(pathlib.Path(args.input).name),
        "loop_index": final_loop_index,
        "query_type": query_type,
        "main_result": None,
        "main_time": None,
        "main_quantifiers": None,
        "main_atoms": None,
        "main_size": None,
        "main_variables": None,
        "main_arrays": None,
        "negated_result": None,
        "negated_time": None,
        "negated_quantifiers": None,
        "negated_atoms": None,
        "negated_size": None,
        "negated_variables": None,
        "negated_arrays": None,
        "conclusion": None,
    }

    print("\n--- Solving Primary Query ---")
    main_result_str = "UNKNOWN"
    try:
        main_result = solve_smt_string(smt_query, args.timeout)
        main_is_sat = main_result.is_sat
        main_result_str = "SAT" if main_is_sat else "UNSAT"

        run_data["main_result"] = main_result_str
        run_data["main_time"] = main_result.time_elapsed
        run_data["main_quantifiers"] = main_result.num_quantifiers
        run_data["main_atoms"] = main_result.num_atoms
        run_data["main_size"] = main_result.formula_size
        run_data["main_variables"] = main_result.num_variables
        run_data["main_arrays"] = main_result.num_arrays

        print(
            f"Primary Query Result: {main_result_str} (Time: {main_result.time_elapsed:.4f}s, "
            f"Quantifiers: {main_result.num_quantifiers}, Atoms: {main_result.num_atoms}, "
            f"Size: {main_result.formula_size}, Vars: {main_result.num_variables}, Arrays: {main_result.num_arrays})"
        )
    except (SolverReturnedUnknownResultError, TimeoutError):
        # Retry with aggressive=True
        print("Primary Query Result: UNKNOWN/TIMEOUT. Retrying with aggressive=True...")
        try:
            main_result = solve_smt_string(smt_query, args.timeout, aggressive=True)
            main_is_sat = main_result.is_sat
            main_result_str = "SAT" if main_is_sat else "UNSAT"

            run_data["main_result"] = main_result_str
            run_data["main_time"] = main_result.time_elapsed
            run_data["main_quantifiers"] = main_result.num_quantifiers
            run_data["main_atoms"] = main_result.num_atoms
            run_data["main_size"] = main_result.formula_size
            run_data["main_variables"] = main_result.num_variables
            run_data["main_arrays"] = main_result.num_arrays

            print(
                f"Primary Query Result (aggressive retry): {main_result_str} (Time: {main_result.time_elapsed:.4f}s, "
                f"Quantifiers: {main_result.num_quantifiers}, Atoms: {main_result.num_atoms}, "
                f"Size: {main_result.formula_size}, Vars: {main_result.num_variables}, Arrays: {main_result.num_arrays})"
            )
        except SolverReturnedUnknownResultError:
            print(
                "Primary Query Result (aggressive retry): UNKNOWN (Solver returned unknown)"
            )
            main_result_str = "UNKNOWN"
            run_data["main_result"] = "UNKNOWN"
        except TimeoutError:
            print("Primary Query Result (aggressive retry): UNKNOWN (Timeout)")
            main_result_str = "TIMEOUT"
            run_data["main_result"] = "TIMEOUT"
        except Exception as e:
            print(f"Primary Query Result (aggressive retry): ERROR - {e}")
            main_result_str = f"ERROR: {str(e)}"
            run_data["main_result"] = main_result_str
    except Exception as e:
        print(f"Primary Query Result: ERROR - {e}")
        main_result_str = f"ERROR: {str(e)}"
        run_data["main_result"] = main_result_str

    if negated_query:
        print("\n--- Solving Negated Query ---")
        negated_result_str = "UNKNOWN"
        try:
            negated_result = solve_smt_string(negated_query, args.timeout)
            negated_is_sat = negated_result.is_sat
            negated_result_str = "SAT" if negated_is_sat else "UNSAT"

            run_data["negated_result"] = negated_result_str
            run_data["negated_time"] = negated_result.time_elapsed
            run_data["negated_quantifiers"] = negated_result.num_quantifiers
            run_data["negated_atoms"] = negated_result.num_atoms
            run_data["negated_size"] = negated_result.formula_size
            run_data["negated_variables"] = negated_result.num_variables
            run_data["negated_arrays"] = negated_result.num_arrays

            print(
                f"Negated Query Result: {negated_result_str} (Time: {negated_result.time_elapsed:.4f}s, "
                f"Quantifiers: {negated_result.num_quantifiers}, Atoms: {negated_result.num_atoms}, "
                f"Size: {negated_result.formula_size}, Vars: {negated_result.num_variables}, Arrays: {negated_result.num_arrays})"
            )
        except (SolverReturnedUnknownResultError, TimeoutError):
            # Retry with aggressive=True
            print(
                "Negated Query Result: UNKNOWN/TIMEOUT. Retrying with aggressive=True..."
            )
            try:
                negated_result = solve_smt_string(
                    negated_query, args.timeout, aggressive=True
                )
                negated_is_sat = negated_result.is_sat
                negated_result_str = "SAT" if negated_is_sat else "UNSAT"

                run_data["negated_result"] = negated_result_str
                run_data["negated_time"] = negated_result.time_elapsed
                run_data["negated_quantifiers"] = negated_result.num_quantifiers
                run_data["negated_atoms"] = negated_result.num_atoms
                run_data["negated_size"] = negated_result.formula_size
                run_data["negated_variables"] = negated_result.num_variables
                run_data["negated_arrays"] = negated_result.num_arrays

                print(
                    f"Negated Query Result (aggressive retry): {negated_result_str} (Time: {negated_result.time_elapsed:.4f}s, "
                    f"Quantifiers: {negated_result.num_quantifiers}, Atoms: {negated_result.num_atoms}, "
                    f"Size: {negated_result.formula_size}, Vars: {negated_result.num_variables}, Arrays: {negated_result.num_arrays})"
                )
            except SolverReturnedUnknownResultError:
                print(
                    "Negated Query Result (aggressive retry): UNKNOWN (Solver returned unknown)"
                )
                negated_result_str = "UNKNOWN"
                run_data["negated_result"] = "UNKNOWN"
            except TimeoutError:
                print("Negated Query Result (aggressive retry): UNKNOWN (Timeout)")
                negated_result_str = "TIMEOUT"
                run_data["negated_result"] = "TIMEOUT"
            except Exception as e:
                print(f"Negated Query Result (aggressive retry): ERROR - {e}")
                negated_result_str = f"ERROR: {str(e)}"
                run_data["negated_result"] = negated_result_str
        except Exception as e:
            print(f"Negated Query Result: ERROR - {e}")
            negated_result_str = f"ERROR: {str(e)}"
            run_data["negated_result"] = negated_result_str

        print("\n--- Interpretation ---")
        conclusion = "Inconclusive"
        if main_result_str == "SAT" and negated_result_str == "UNSAT":
            conclusion = "Holds (No Counterexample)"
            print("Conclusion: The property (D-FS/B) holds. No counterexample found.")
        elif main_result_str == "UNSAT" and negated_result_str == "SAT":
            conclusion = "Does Not Hold (Counterexample Found)"
            print(
                "Conclusion: The property (D-FS/B) does NOT hold. A counterexample (witness) was found."
            )
        elif main_result_str == "UNKNOWN" and negated_result_str == "SAT":
            conclusion = "Does Not Hold (Counterexample Found - Interpreted)"
            print(
                "Conclusion: Primary query UNKNOWN, but negated query SAT. Interpreting primary as UNSAT."
            )
            print(
                "            The property (D-FS/B) does NOT hold. A counterexample (witness) was found."
            )
        elif main_result_str == "UNKNOWN" and negated_result_str == "UNSAT":
            conclusion = "Holds (No Counterexample - Interpreted)"
            print(
                "Conclusion: Primary query UNKNOWN, but negated query UNSAT. Interpreting primary as SAT."
            )
            print("            The property (D-FS/B) holds. No counterexample found.")
        elif main_result_str == "UNKNOWN" or negated_result_str == "UNKNOWN":
            conclusion = "Inconclusive (UNKNOWN)"
            print(
                "Conclusion: At least one query returned UNKNOWN. Cannot provide a definitive interpretation."
            )
        else:
            conclusion = "Inconclusive (Inconsistent)"
            print(
                f"Conclusion: Results are inconclusive or indicate an issue with query generation/solver consistency."
            )
            print(
                f"            Primary: {main_result_str}, Negated: {negated_result_str}"
            )
        run_data["conclusion"] = conclusion

    elif main_result_str == "UNKNOWN":
        run_data["conclusion"] = "Inconclusive (UNKNOWN)"
        print(
            f"Conclusion: Only primary query was run, and it returned UNKNOWN. Cannot provide a definitive interpretation."
        )
    else:
        # For single query types, we can often infer something, but without a specific mapping for each type,
        # we might just leave conclusion as None or "Primary Result Only".
        # Actually, for D-FS (exists data...), SAT means "Yes, exists". UNSAT means "No".
        # For now, I'll just store the primary result.
        pass

    if args.db:
        print(f"\nLogging results to database: {args.db}")
        try:
            log_to_db(args.db, run_data)
            print("Successfully logged to database.")
        except Exception as e:
            print(f"Error logging to database: {e}")


if __name__ == "__main__":
    main()
