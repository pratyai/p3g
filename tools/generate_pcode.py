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

    original_input_arg = args.input

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

    # Determine output path if not provided or if it's a directory
    if args.output is None:
        input_path = pathlib.Path(args.input)
        if os.path.isdir(original_input_arg):
            # If original input was a directory, use it as the output directory
            output_dir = pathlib.Path(original_input_arg)
        else:
            # Otherwise, use the default project_root/tmp
            output_dir = pathlib.Path(project_root) / "tmp"
        output_dir.mkdir(parents=True, exist_ok=True)  # Ensure tmp directory exists
        output_file_path = output_dir / f"{input_path.stem}.pcode"
    else:
        output_path = pathlib.Path(args.output)
        if output_path.is_dir():
            input_path = pathlib.Path(args.input)
            output_path.mkdir(
                parents=True, exist_ok=True
            )  # Ensure output directory exists
            output_file_path = output_path / f"{input_path.stem}.pcode"
        else:
            # Assume it's a file path, ensure its parent directory exists
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_file_path = output_path

    print(f"Loading SDFG from {args.input}")
    sdfg = dace.SDFG.from_file(args.input)

    print(f"Converting SDFG '{sdfg.name}' to pseudocode...")
    converter = SDFGToPseudocodeConverter(sdfg)
    pseudocode = converter.convert()

    with open(output_file_path, "w") as f:
        f.write(pseudocode)

    print(f"Pseudocode generated and saved to {output_file_path}")


if __name__ == "__main__":
    main()
