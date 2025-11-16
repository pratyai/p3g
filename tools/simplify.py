import argparse
import os
import glob
from z3 import *


def simplify_smt_file(input_file, readable_dir, smt2_dir, timeout_ms):
    """
    Simplifies a single SMT2 file, verifies the simplification,
    and saves two versions of the output.
    """
    base_filename = os.path.basename(input_file)
    readable_path = os.path.join(readable_dir, base_filename)
    smt2_path = os.path.join(smt2_dir, base_filename)

    print(f"Processing {input_file}...")

    try:
        # --- Load SMT file ---
        with open(input_file) as f:
            smt_str = f.read()

        # --- 1. Check original formula ---
        original_solver = Solver()
        original_solver.set(timeout=timeout_ms)
        original_solver.from_string(smt_str)
        original_result = original_solver.check()
        if original_result == unknown:
            print(
                f"  -> Original check timed out after {timeout_ms / 1000} seconds. Skipping file."
            )
            return
        print(f"  -> Original result: {original_result}")

        # --- 2. Simplify assertions ---
        simplified_asserts = []
        seen = set()
        for a in original_solver.assertions():
            s = simplify(a)
            s_sexpr = s.sexpr()
            if s_sexpr not in seen:
                seen.add(s_sexpr)
                simplified_asserts.append(s)

        # --- 3. Check simplified solver ---
        simplified_solver = Solver()
        simplified_solver.set(timeout=timeout_ms)
        simplified_solver.add(simplified_asserts)
        simplified_result = simplified_solver.check()
        if simplified_result == unknown:
            print(
                f"  -> Simplified check timed out after {timeout_ms / 1000} seconds. Skipping file."
            )
            return
        print(f"  -> Simplified result: {simplified_result}")
        assert original_result == simplified_result, (
            "Simplification changed the satisfiability!"
        )

        # --- 4. Generate and save outputs ---
        # Readable output
        readable_output = "\n".join([str(a) for a in simplified_solver.assertions()])
        if simplified_result == sat:
            model = simplified_solver.model()
            readable_output += "\n\n--- Model (Witness) ---\n"
            for d in model.decls():
                readable_output += f"{d.name()} = {model[d]}\n"

        with open(readable_path, "w") as f:
            f.write(readable_output)

        # SMT-LIB v2 output
        output_solver = Solver()
        output_solver.add(simplified_asserts)
        smt2_output = output_solver.sexpr()
        with open(smt2_path, "w") as f:
            f.write(smt2_output)

        # --- 5. Verify the final SMT-LIB string ---
        final_checker = Solver()
        final_checker.set(timeout=timeout_ms)
        final_checker.from_string(smt2_output)
        final_result = final_checker.check()
        if final_result == unknown:
            print(
                f"  -> Final SMT output check timed out after {timeout_ms / 1000} seconds. Output may be invalid."
            )
            return
        print(f"  -> Final SMT output result: {final_result}")
        assert original_result == final_result, (
            "Final SMT output changed the satisfiability!"
        )

        print(f"  -> All checks passed. Saved outputs.")

    except Exception as e:
        print(f"  -> Error processing {input_file}: {e}")


def main():
    parser = argparse.ArgumentParser(description="Simplify SMT2 files in a directory.")
    parser.add_argument(
        "-i",
        "--input_dir",
        required=True,
        help="Input directory containing .smt2 files.",
    )
    parser.add_argument(
        "-o",
        "--output_dir",
        required=True,
        help="Output directory to save simplified files.",
    )
    parser.add_argument(
        "-t",
        "--timeout",
        type=int,
        default=10,
        help="Timeout in seconds for each SMT check. Default: 30 seconds.",
    )
    args = parser.parse_args()

    # --- Validate directories ---
    if not os.path.isdir(args.input_dir):
        print(f"Error: Input directory not found at '{args.input_dir}'")
        exit(1)

    # --- Create output directories ---
    readable_dir = os.path.join(args.output_dir, "readable")
    smt2_dir = os.path.join(args.output_dir, "smt2")
    os.makedirs(readable_dir, exist_ok=True)
    os.makedirs(smt2_dir, exist_ok=True)

    print(f"Input directory:  {args.input_dir}")
    print(f"Output directory: {args.output_dir}")
    print("-" * 20)

    # --- Find and process files ---
    smt2_files = glob.glob(os.path.join(args.input_dir, "*.smt2"))
    if not smt2_files:
        print("No .smt2 files found in the input directory.")
        return

    timeout_ms = args.timeout * 1000
    for smt2_file in smt2_files:
        simplify_smt_file(smt2_file, readable_dir, smt2_dir, timeout_ms)

    print("-" * 20)
    print("Processing complete.")


if __name__ == "__main__":
    main()
