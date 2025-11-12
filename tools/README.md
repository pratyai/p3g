# SMT Simplification Tool

This directory contains `simplify.py`, a command-line tool for batch-processing and simplifying SMT-LIB v2 files using the Z3 solver.

## Description

The script finds all `.smt2` files in a specified input directory, applies Z3's `simplify` engine to each assertion, and then saves two different versions of the simplified output to a specified output directory. It also verifies that the simplification process does not change the satisfiability (`sat` or `unsat`) of the original formula.

## Features

- Simplifies all `.smt2` files in a directory (non-recursively).
- Verifies that the satisfiability of the formula is preserved after simplification.
- Generates two distinct output formats for each input file:
    1.  **Human-Readable:** A plain text file containing the simplified assertions, with each assertion on a new line.
    2.  **SMT-LIB v2:** A formal, self-contained `.smt2` file that can be parsed by any SMT-LIB compliant solver.

## Usage

```sh
python3 tools/simplify.py -i <input_dir> -o <output_dir>
```

### Arguments

-   `-i, --input_dir`: (Required) The path to the directory containing the input `.smt2` files.
-   `-o, --output_dir`: (Required) The path to the directory where the output files will be saved.

## Example Usage

To simplify all `.smt2` files in the `tmp/smt` directory and save the output to `tmp/smt_simplified`:

```sh
python3 tools/simplify.py -i tmp/smt -o tmp/smt_simplified
```

## Output Structure

The tool will create the output directory if it doesn't exist, along with two subdirectories inside it: `readable` and `smt2`.

```
<output_dir>/
├── readable/
│   ├── file1.smt2
│   └── ...
└── smt2/
    ├── file1.smt2
    └── ...
```

-   **`readable/`**: Contains the simplified assertions in a human-readable, one-assertion-per-line format.
-   **`smt2/`**: Contains the simplified assertions in the formal SMT-LIB v2 format.

## Dependencies

This tool requires the `z3-solver` Python package. You can install it and other project dependencies from the `requirements.txt` file:

```sh
pip install -r requirements.txt
```
