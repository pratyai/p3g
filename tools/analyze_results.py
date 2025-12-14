import sqlite3
import re
import os
import collections

# Paths
CLOUDSC_DB = "tools/demo/cloudsc-sdfg/smt/cloudsc-results.sqlite"
CLOUDSC_INIT = "tools/demo/cloudsc-sdfg/cloudsc.pcode"
CLOUDSC_SSA = "tools/demo/cloudsc-sdfg/cloudsc_expanded.pcode"
CLOUDSC_FINAL = "tools/demo/cloudsc-sdfg/cloudsc_map.pcode"

NPBENCH_DB = "tools/demo/npbench-sdfg/smt/npbench-results.sqlite"
NPBENCH_DIR = "tools/demo/npbench-sdfg"


def get_loop_info(pcode_path):
    """Parses pcode to return a list of dicts with loop info (type, label, variable) in order."""
    loops = []
    if not os.path.exists(pcode_path):
        return loops

    with open(pcode_path, "r") as f:
        for line in f:
            # Match L<id>| for <var> or M<id>| map <var>
            # Regex captures: 1=LabelPrefix(L/M), 2=ID, 3=Type(for/map), 4=VarName
            match = re.search(r"([LM])(\d+)\|\s+(for|map)\s+(\S+)\s*=", line)
            if match:
                loops.append(
                    {
                        "label_prefix": match.group(1),
                        "id": int(match.group(2)),
                        "type": match.group(3),  # 'for' or 'map'
                        "var": match.group(4),
                    }
                )
    return loops


def classify_loops(db_path, input_filename, loops_metadata):
    """Queries DB to classify loops based on metadata order."""
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()

    stats = {
        "total": len(loops_metadata),
        "reducible": 0,
        "irreducible": 0,
        "undecided": 0,
        "timeouts": 0,
        "reducible_indices": [],
        "irreducible_indices": [],  # Indices in the file/DB
        "irreducible_vars": set(),  # Variables of irreducible loops
        "reducible_vars": set(),  # Variables of reducible loops
        "max_time": 0.0,
    }

    for i, loop in enumerate(loops_metadata):
        cursor.execute(
            f"SELECT main_result, negated_result, main_time FROM runs WHERE input_file='{input_filename}' AND loop_index={i}"
        )
        row = cursor.fetchone()

        if row:
            main_res, neg_res, time = row
            if time and time > stats["max_time"]:
                stats["max_time"] = time

            # Verdict Logic
            verdict = "UNDECIDED"
            if main_res == "UNSAT":
                verdict = "REDUCIBLE"
            elif main_res == "SAT":
                verdict = "IRREDUCIBLE"
            elif main_res in ["TIMEOUT", "UNKNOWN"]:
                stats["timeouts"] += 1
                if neg_res == "SAT":
                    verdict = "REDUCIBLE"
                elif neg_res == "UNSAT":
                    verdict = "IRREDUCIBLE"

            if verdict == "REDUCIBLE":
                stats["reducible"] += 1
                stats["reducible_indices"].append(i)
                stats["reducible_vars"].add(loop["var"])
            elif verdict == "IRREDUCIBLE":
                stats["irreducible"] += 1
                stats["irreducible_indices"].append(i)
                stats["irreducible_vars"].add(loop["var"])
            else:
                stats["undecided"] += 1
        else:
            pass

    conn.close()
    return stats


def get_time_stats(db_path, problem_name):
    """Retrieves max, mean, and median main_time for a given problem across all its phases."""
    stats = {"max": 0.0, "mean": 0.0, "median": 0.0}
    if not os.path.exists(db_path):
        return stats

    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()

    # Use LIKE to match all pcode files belonging to the problem
    cursor.execute(
        f"SELECT main_time FROM runs WHERE input_file LIKE '{problem_name}%' AND main_time IS NOT NULL"
    )
    times = [row[0] for row in cursor.fetchall()]

    conn.close()

    if times:
        stats["max"] = max(times)
        stats["mean"] = sum(times) / len(times)

        sorted_times = sorted(times)
        n = len(sorted_times)
        if n % 2 == 1:
            stats["median"] = sorted_times[n // 2]
        else:
            stats["median"] = (sorted_times[n // 2 - 1] + sorted_times[n // 2]) / 2.0

    return stats


def analyze_cloudsc():
    print("--- CLOUDSC Analysis ---")

    # 1. Init
    init_loops = get_loop_info(CLOUDSC_INIT)
    init_stats = classify_loops(CLOUDSC_DB, "cloudsc.pcode", init_loops)

    # 2. Post-SSA (Expanded)
    ssa_loops = get_loop_info(CLOUDSC_SSA)
    ssa_stats = classify_loops(CLOUDSC_DB, "cloudsc_expanded.pcode", ssa_loops)

    # 3. Final (Map) - Structural check only
    final_loops = get_loop_info(CLOUDSC_FINAL)
    final_maps = [l for l in final_loops if l["type"] == "map"]
    final_map_vars = set(l["var"] for l in final_maps)

    # 4. Cross-Reference Analysis

    # A: Forced Maps (Irreducible in SSA -> Became Map)
    forced_maps_vars = ssa_stats["irreducible_vars"].intersection(final_map_vars)

    # B: Realized Parallelism (Reducible in SSA -> Became Map)
    realized_maps_vars = ssa_stats["reducible_vars"].intersection(final_map_vars)

    # C: Lost Parallelism (Reducible in SSA -> Did NOT become Map)
    lost_parallelism_vars = ssa_stats["reducible_vars"] - final_map_vars

    # D: New Maps (Not in SSA loops? e.g. tiling/generated)
    # final_maps_vars - (ssa_reducible + ssa_irreducible)
    all_ssa_vars = ssa_stats["reducible_vars"].union(ssa_stats["irreducible_vars"])
    new_maps_vars = final_map_vars - all_ssa_vars

    final_map_count = len(
        [l for l in final_loops if l["type"] == "map"]
    )  # Count only actual maps

    # Get overall time stats
    time_stats = get_time_stats(CLOUDSC_DB, "cloudsc")

    print(f"Total Loops (SSA): {ssa_stats['total']}")
    print(f"Reducible (Init): {init_stats['reducible']}")
    print(f"Reducible (Post-SSA): {ssa_stats['reducible']}")
    print(f"Irreducible (Post-SSA): {ssa_stats['irreducible']}")
    print(f"Undecided: {ssa_stats['undecided']}")
    print(f"Final Maps (Code): {final_map_count}")
    print("-" * 20)
    print(f"1. Realized Maps (Reducible -> Map): {len(realized_maps_vars)}")
    print(f"2. Forced Maps (Irreducible -> Map): {len(forced_maps_vars)}")
    print(f"3. Lost Parallelism (Reducible -> Loop/Gone): {len(lost_parallelism_vars)}")
    print(f"4. New/Generated Maps (No SSA equivalent): {len(new_maps_vars)}")
    print("-" * 20)
    print(
        f"Check: Realized({len(realized_maps_vars)}) + Forced({len(forced_maps_vars)}) + New({len(new_maps_vars)}) = {len(realized_maps_vars) + len(forced_maps_vars) + len(new_maps_vars)} (Should be close to {final_map_count})"
    )
    print(
        f"Time Stats: Max={time_stats['max']:.4f}s, Mean={time_stats['mean']:.4f}s, Median={time_stats['median']:.4f}s"
    )

    return {
        "total": ssa_stats["total"],
        "init_red": init_stats["reducible"],
        "ssa_red": ssa_stats["reducible"],
        "final_maps": final_map_count,
        "time_stats": time_stats,
    }


def analyze_npbench():
    print("\n--- NPBench Analysis ---")
    problems = ["adi", "gram_schmidt", "heat3d", "spmv"]
    results = {}

    for prob in problems:
        # File paths
        init_pcode = os.path.join(NPBENCH_DIR, f"{prob}.pcode")
        ssa_pcode = os.path.join(NPBENCH_DIR, f"{prob}_expanded.pcode")
        final_pcode = os.path.join(NPBENCH_DIR, f"{prob}_map.pcode")

        # Get Info
        init_loops = get_loop_info(init_pcode)
        ssa_loops = get_loop_info(ssa_pcode)
        final_loops = get_loop_info(final_pcode)

        # Classify
        init_stats = classify_loops(NPBENCH_DB, f"{prob}.pcode", init_loops)
        ssa_stats = classify_loops(NPBENCH_DB, f"{prob}_expanded.pcode", ssa_loops)

        final_map_count = len([l for l in final_loops if l["type"] == "map"])

        # Get time stats
        time_stats = get_time_stats(NPBENCH_DB, prob)

        results[prob] = {
            "total": init_stats["total"],
            "init_red": init_stats["reducible"],
            "ssa_red": ssa_stats["reducible"],
            "final_maps": final_map_count,
            "time_stats": time_stats,
        }

        print(f"Problem: {prob}")
        print(f"  Total Loops: {init_stats['total']}")
        print(f"  Reducible (Init): {init_stats['reducible']}")
        print(f"  Reducible (SSA): {ssa_stats['reducible']}")
        print(f"  Final Maps: {final_map_count}")
        print(
            f"  Time Stats: Max={time_stats['max']:.4f}s, Mean={time_stats['mean']:.4f}s, Median={time_stats['median']:.4f}s"
        )


if __name__ == "__main__":
    analyze_cloudsc()
    analyze_npbench()
