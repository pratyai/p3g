import re
import sqlite3

pcode_file = "tools/demo/cloudsc-sdfg/cloudsc_expanded.pcode"
db_file = "tools/demo/cloudsc-sdfg/smt/cloudsc-results.sqlite"

# 1. Parse PCode to find loops
loops = []
with open(pcode_file, "r") as f:
    lines = f.readlines()
    for i, line in enumerate(lines):
        # Look for lines like: ... L16| for ...
        match = re.search(r"L(\d+)\|\s*for\s+", line)
        if match:
            loops.append(
                {
                    "index": len(loops),
                    "label": f"L{match.group(1)}",
                    "line_num": i + 1,
                    "content": line.strip(),
                }
            )

print(f"Found {len(loops)} loops in pcode.")

# 2. Connect to DB
conn = sqlite3.connect(db_file)
cursor = conn.cursor()

# 3. Analyze Timeouts
timeout_indices = [82, 96, 102, 109, 168]
print("\n--- Timeout Loops Analysis ---")
for idx in timeout_indices:
    if idx < len(loops):
        loop = loops[idx]
        print(f"\nLoop Index: {idx} (Label: {loop['label']}, Line: {loop['line_num']})")
        print(f"Code: {loop['content']}")

        # Get DB stats
        cursor.execute(
            "SELECT * FROM runs WHERE input_file='cloudsc_expanded.pcode' AND loop_index=?",
            (idx,),
        )
        row = cursor.fetchone()
        if row:
            # Row structure: id, timestamp, file, idx, type, res, time, quants, atoms, size, vars, arrays, ...
            print(f"SMT Result: {row[5]}")
            print(f"Metrics: Quantifiers={row[7]}, Atoms={row[8]}, Vars={row[10]}")
            print(f"Negated Result: {row[12]} (Time: {row[13]}s)")

# 4. Analyze Most Complex Loops (by Quantifiers)
print("\n--- Top 5 Most Complex Loops (by Quantifiers) ---")
cursor.execute(
    "SELECT loop_index, main_result, main_quantifiers, main_atoms, main_variables FROM runs WHERE input_file='cloudsc_expanded.pcode' ORDER BY main_quantifiers DESC LIMIT 5"
)
complex_loops = cursor.fetchall()

for row in complex_loops:
    idx = row[0]
    if idx < len(loops):
        loop = loops[idx]
        print(f"\nLoop Index: {idx} (Label: {loop['label']}, Line: {loop['line_num']})")
        print(f"Code: {loop['content']}")
        print(f"Result: {row[1]}")
        print(f"Complexity: Quantifiers={row[2]}, Atoms={row[3]}, Vars={row[4]}")

conn.close()
