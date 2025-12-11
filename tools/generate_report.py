import sqlite3
import os

DB_PATH = "tools/demo/npbench/results.db"
REPORT_PATH = "REPORT.md"


def generate_report():
    if not os.path.exists(DB_PATH):
        print(f"Database not found at {DB_PATH}")
        return

    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()

    query = """
    SELECT 
        input_file,
        loop_index,
        query_type,
        conclusion,
        main_result,
        main_variables,
        main_quantifiers,
        negated_result,
        printf('%.4f', main_time),
        printf('%.4f', negated_time)
    FROM runs
    ORDER BY input_file, loop_index
    """

    cursor.execute(query)
    rows = cursor.fetchall()

    # Headers mapping
    headers = [
        "Problem",
        "Loop",
        "Query",
        "Conclusion",
        "Main Res",
        "Variables",
        "Quantifiers",
        "Neg Res",
        "Main Time(s)",
        "Neg Time(s)",
    ]

    conn.close()

    # Format the markdown
    md = "# NPBench Loop Analysis Report\n\n"
    md += "This report summarizes the SMT-based dependency analysis of the main outer loops in various NPBench kernels.\n\n"
    md += "## Summary of Results\n\n"

    # Table Header
    md += "| " + " | ".join(headers) + " |\n"
    md += "| " + " | ".join(["---"] * len(headers)) + " |\n"

    # Table Body
    for row in rows:
        # Clean up filename (remove .pcode)
        problem = row[0].replace(".pcode", "")
        new_row = [problem] + list(row[1:])
        row_str = [str(item) if item is not None else "-" for item in new_row]
        md += "| " + " | ".join(row_str) + " |\n"

    md += "\n\n## Interpretation Key\n"
    md += "- **Holds (No Counterexample)**: The property (e.g., Full Seriality) is proven to hold for all inputs/bounds.\n"
    md += "- **Does Not Hold**: A counterexample (witness) was found where the property is violated.\n"
    md += "- **Inconclusive**: The solver returned UNKNOWN or timed out.\n"

    with open(REPORT_PATH, "w") as f:
        f.write(md)

    print(f"Report generated at {REPORT_PATH}")


if __name__ == "__main__":
    generate_report()
