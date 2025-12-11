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
input_pcode_path = os.path.join(project_root, "tools", "demo", "cloudsc.pcode")

CMD = [
    sys.executable,
    generate_smt_path,
    "-i",
    input_pcode_path,
    "-q",
    "D-FS/B",
    "-l",
    None,
]  # placeholder

RESULT_RE = re.compile(r"Primary Query Result:\s*(.*)")

results = {}

for num in range(0, 146):
    print(f"Running NUM={num} ...", flush=True)

    cmd = CMD.copy()
    cmd[cmd.index(None)] = str(num)

    try:
        out = subprocess.check_output(cmd, stderr=subprocess.STDOUT, text=True)
    except subprocess.CalledProcessError as e:
        out = e.output  # still read output even if return code != 0

    match = RESULT_RE.search(out)
    if match:
        result = match.group(1).strip()
    else:
        result = "<NO RESULT FOUND>"

    results[num] = result

# Print in a simple map form
output_filename = os.path.join(project_root, "cloudsc_results.txt")
with open(output_filename, "w") as f:
    for k in sorted(results):
        line = f"{k}: {results[k]}"
        print(line)  # Also print to console
        f.write(line + "\n")
print(f"\nResults written to {output_filename}")
