import sqlite3
import collections
import os
import re

# Paths
NPBENCH_DB = "tools/demo/npbench-sdfg/smt/npbench-results.sqlite"
CLOUDSC_DB = "tools/demo/cloudsc-sdfg/smt/cloudsc-results.sqlite"


def get_structural_types(pcode_path):
    """Parses pcode to return a list of 'For' or 'Map' based on structural appearance."""
    types = []
    if not os.path.exists(pcode_path):
        print(f"Warning: Structural analysis file not found: {pcode_path}")
        return types

    with open(pcode_path, "r") as f:
        for line in f:
            if "| for" in line:
                loop_var = line.split("| for ")[1].split(" =")[0]
                types.append(("For", loop_var))
            elif "| map" in line:
                loop_var = line.split("| map ")[1].split(" =")[0]
                types.append(("Map", loop_var))

    print(f"DEBUG: Found {len(types)} structural loops in {pcode_path}")
    return types


def analyze_all_side_by_side():
    # Define problem classes and their corresponding DBs and directories
    problem_configs = {
        "adi": {"db": NPBENCH_DB, "dir": "tools/demo/npbench-sdfg"},
        "gram_schmidt": {"db": NPBENCH_DB, "dir": "tools/demo/npbench-sdfg"},
        "heat3d": {"db": NPBENCH_DB, "dir": "tools/demo/npbench-sdfg"},
        "spmv": {"db": NPBENCH_DB, "dir": "tools/demo/npbench-sdfg"},
        "cloudsc": {
            "db": CLOUDSC_DB,
            "dir": "tools/demo/cloudsc-sdfg",
        },  # Special case for cloudsc
    }

    # Identify all problem classes to process (from problem_configs keys)
    problems = sorted(list(problem_configs.keys()))

    for prob in problems:
        print(f"\n=== Problem: {prob} ===")

        db_path = problem_configs[prob]["db"]
        prob_dir = problem_configs[prob]["dir"]

        if not os.path.exists(db_path):
            print(f"  Database not found for {prob}: {db_path}")
            continue

        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()

        # Define the four phases explicitly
        phases_config = collections.OrderedDict(
            [
                ("Initial", f"{prob}.pcode"),
                ("Expanded (SSA)", f"{prob}_expanded.pcode"),
                ("Initial Map", f"{prob}_initial_map.pcode"),  # The missed phase
                ("Final Map", f"{prob}_map.pcode"),
            ]
        )

        final_map_file = os.path.join(prob_dir, f"{prob}_map.pcode")
        structural_types = get_structural_types(final_map_file)
        loop_vars = [v for u, v in structural_types]
        structural_types = [u for u, v in structural_types]

        results = collections.defaultdict(dict)

        # Verify which phases actually exist as files and in the DB for this problem
        existing_phases_for_problem = []
        for phase_name, filename_pattern in phases_config.items():
            full_path = os.path.join(prob_dir, filename_pattern)

            # Check if the file exists and if there are results for it in the DB
            cursor.execute(
                f"SELECT COUNT(*) FROM runs WHERE input_file='{filename_pattern}'"
            )
            if cursor.fetchone()[0] > 0:  # If there are results in the DB
                existing_phases_for_problem.append(phase_name)

                cursor.execute(
                    f"SELECT loop_index, main_result FROM runs WHERE input_file='{filename_pattern}' ORDER BY loop_index"
                )
                for loop_idx, main_result in cursor.fetchall():
                    results[loop_idx][phase_name] = main_result

        if not results:
            print("  No loop data found for any phase.")
            conn.close()
            continue

        max_loop_idx = max(results.keys())

        # Header
        header_str = f"{'Idx':<5}"
        for col in existing_phases_for_problem:
            header_str += f" | {col:<15}"
        header_str += f" | {'Structural':<10} | {'Loop Var':<20}"
        print(header_str)
        print("-" * len(header_str))

        # Rows
        for i in range(max_loop_idx + 1):
            row_str = f"{i:<5}"
            has_data_in_row = False
            for ph in existing_phases_for_problem:
                val = results[i].get(ph, "")
                if val:
                    has_data_in_row = True
                row_str += f" | {val:<15}"

            # Structural info
            struct_val = structural_types[i] if i < len(structural_types) else "N/A"
            loop_var_val = loop_vars[i] if i < len(loop_vars) else "N/A"

            final_map_res = results[i].get("Final Map", "")
            marker = ""
            if final_map_res and struct_val in ["For", "Map"]:
                # Consistent: (SAT -> For) or (UNSAT -> Map)
                is_consistent = (final_map_res == "SAT" and struct_val == "For") or (
                    final_map_res == "UNSAT" and struct_val == "Map"
                )
                if not is_consistent:
                    marker = " (*)"

            struct_display = f"{struct_val}{marker}"
            row_str += f" | {struct_display:<10} | {loop_var_val:<20}"

            if has_data_in_row:  # Only print rows that actually have data
                print(row_str)

        # Transition Analysis
        print("-" * len(header_str))
        print("Transitions:")

        transitions_to_check = [("Init", "Expanded"), ("Expanded", "FinalMap")]

        for p1, p2 in transitions_to_check:
            # Need to match phase names from phases_config keys to existing_phases_for_problem
            p1_key = None
            p2_key = None

            if p1 == "Init":
                p1_key = "Initial"
            elif p1 == "Expanded":
                p1_key = "Expanded (SSA)"
            elif p1 == "FinalMap":
                p1_key = "Final Map"

            if p2 == "Init":
                p2_key = "Initial"
            elif p2 == "Expanded":
                p2_key = "Expanded (SSA)"
            elif p2 == "FinalMap":
                p2_key = "Final Map"

            if (
                p1_key in existing_phases_for_problem
                and p2_key in existing_phases_for_problem
            ):
                sat_to_unsat = 0
                unsat_to_sat = 0
                sat_to_sat = 0
                unsat_to_unsat = 0

                for i in range(max_loop_idx + 1):
                    v1 = results[i].get(p1_key, "")
                    v2 = results[i].get(p2_key, "")

                    if v1 and v2:
                        if v1 == "SAT" and v2 == "UNSAT":
                            sat_to_unsat += 1
                        elif v1 == "UNSAT" and v2 == "SAT":
                            unsat_to_sat += 1
                        elif v1 == "SAT" and v2 == "SAT":
                            sat_to_sat += 1
                        elif v1 == "UNSAT" and v2 == "UNSAT":
                            unsat_to_unsat += 1

                print(f"  {p1} -> {p2}:")
                print(f"    SAT -> UNSAT (Resolved): {sat_to_unsat}")
                print(f"    UNSAT -> SAT (Regressed): {unsat_to_sat}")
                print(f"    SAT -> SAT (unchanged):   {sat_to_sat}")
                print(f"    UNSAT -> UNSAT (unchanged): {unsat_to_unsat}")

        # Final Map -> Structural Analysis
        print("  Final Map -> Structural:")
        sat_to_for = 0
        unsat_to_map = 0
        sat_to_map = 0
        unsat_to_for = 0

        # We can only compare up to the number of structural types we found
        limit = min(max_loop_idx + 1, len(structural_types))

        for i in range(limit):
            final_res = results[i].get("Final Map", "")
            struct_type = structural_types[i]

            if final_res and struct_type:
                if final_res == "SAT" and struct_type == "For":
                    sat_to_for += 1
                elif final_res == "UNSAT" and struct_type == "Map":
                    unsat_to_map += 1
                elif final_res == "SAT" and struct_type == "Map":
                    sat_to_map += 1
                elif final_res == "UNSAT" and struct_type == "For":
                    unsat_to_for += 1

        print(f"    SAT -> For (Consistent Sequential): {sat_to_for}")
        print(f"    UNSAT -> Map (Consistent Parallel): {unsat_to_map}")
        print(f"    SAT -> Map (Forced Map): {sat_to_map}")
        print(f"    UNSAT -> For (Lost Parallelism): {unsat_to_for}")

        conn.close()


if __name__ == "__main__":
    analyze_all_side_by_side()
