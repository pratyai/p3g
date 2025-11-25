import argparse
import os
import pathlib
import sys

import dace

# Add the project root to the sys.path
script_dir = os.path.dirname(__file__)
project_root = os.path.abspath(os.path.join(script_dir, os.pardir))
sys.path.insert(0, project_root)

from sdfg.pcode import SDFGToPseudocodeConverter


def main():
    parser = argparse.ArgumentParser(
        description="Generate P3G pseudocode from a DaCe SDFG."
    )
    parser.add_argument(
        "-i",
        "--input",
        required=True,
        help="Input file containing the SDFG (.sdfg or .sdfgz).",
    )
    parser.add_argument(
        "-o",
        "--output",
        help="Output file to write the generated pseudocode. Defaults to <project_root>/tmp/<input_filename_without_extension>.pcode",
    )
    args = parser.parse_args()

    # Handle directory input
    if os.path.isdir(args.input):
        import questionary

        sdfg_files = list(pathlib.Path(args.input).rglob("*.sdfg")) + list(
            pathlib.Path(args.input).rglob("*.sdfgz")
        )

        if not sdfg_files:
            print(f"Error: No .sdfg or .sdfgz files found in '{args.input}'.")
            sys.exit(1)

        choices = [str(f) for f in sdfg_files]

        selected_file = questionary.select(
            "Multiple SDFG files found. Please choose one:",
            choices=sorted(choices),
        ).ask()

        if selected_file is None:
            print("No file selected. Exiting.")
            sys.exit(1)

        args.input = selected_file

    # Determine output path if not provided
    if args.output is None:
        input_path = pathlib.Path(args.input)
        output_dir = pathlib.Path(project_root) / "tmp"
        output_dir.mkdir(parents=True, exist_ok=True)  # Ensure tmp directory exists
        args.output = str(output_dir / f"{input_path.stem}.pcode")

    print(f"Loading SDFG from {args.input}")
    sdfg = dace.SDFG.from_file(args.input)

    print(f"Converting SDFG '{sdfg.name}' to pseudocode...")
    converter = SDFGToPseudocodeConverter(sdfg)
    pseudocode = converter.convert()

    with open(args.output, "w") as f:
        f.write(pseudocode)

    print(f"Pseudocode generated and saved to {args.output}")


if __name__ == "__main__":
    main()
