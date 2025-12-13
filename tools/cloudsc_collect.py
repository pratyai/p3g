#!/usr/bin/env python3
import subprocess
import re
import os
import sys

# Ensure we operate from project root
script_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(script_dir, os.pardir))

# Paths relative to project root
generate_smt_path = os.path.join(project_root, "tools", "generate_smt.py")
input_dir = os.path.join(project_root, "tools", "demo", "cloudsc-sdfg")
output_dir = os.path.join(project_root, "tools", "demo", "cloudsc-sdfg", "smt")
db_path = os.path.join(output_dir, "cloudsc-results.sqlite")

# Ensure output directory exists
os.makedirs(output_dir, exist_ok=True)


def count_loops(filepath):
    """Counts the number of loop/map statements in a pcode file."""
    count = 0
    with open(filepath, "r") as f:
        for line in f:
            if "| for " in line or "| map " in line:
                count += 1
    return count


RESULT_RE = re.compile(r"Primary Query Result:\s*(.*)")

results = {}

# Process all .pcode files in the input directory
pcode_files = [f for f in os.listdir(input_dir) if f.endswith(".pcode")]

for filename in pcode_files:
    input_path = os.path.join(input_dir, filename)
    loop_count = count_loops(input_path)
    print(f"File {filename} has {loop_count} loops.", flush=True)

    for loop_idx in range(loop_count):
        print(f"Running {filename} (Loop {loop_idx}) ...", flush=True)

        output_smt_path = os.path.join(
            output_dir, f"{filename.replace('.pcode', '')}_l{loop_idx}.smt2"
        )

        cmd = [
            sys.executable,
            generate_smt_path,
            "-i",
            input_path,
            "-o",
            output_smt_path,
            "-q",
            "D-FS/B",
            "-l",
            str(loop_idx),
            "-t",
            "60",
            "-db",
            db_path,
        ]

        try:
            out = subprocess.check_output(cmd, stderr=subprocess.STDOUT, text=True)
            match = RESULT_RE.search(out)
            if match:
                result = match.group(1).strip()
            else:
                result = "<NO RESULT FOUND>"
        except subprocess.CalledProcessError as e:
            result = f"ERROR (Code {e.returncode})"
            # print(e.output)

        results[f"{filename} Loop {loop_idx}"] = result

# Print results
output_filename = os.path.join(project_root, "cloudsc_results.txt")
with open(output_filename, "w") as f:
    for k in results:
        line = f"{k}: {results[k]}"
        print(line)
        f.write(line + "\n")
print(f"\nResults written to {output_filename}")
