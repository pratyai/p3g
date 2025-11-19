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
python3 tools/simplify.com -i tmp/smt -o tmp/smt_simplified
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
# SMT Query Generation Tool

This directory also contains `generate_smt.py`, a command-line tool for converting pseudocode into various SMT-LIB v2 queries.

## Description

The script takes a pseudocode input file, parses it into a Program Dependence Graph (P3G), and then generates an SMT-LIB v2 query based on a specified query type. The generated SMT query can then be used with an SMT solver (e.g., Z3) to analyze properties of the program, such as data dependencies.

## Features

- Parses pseudocode to a P3G representation.
- Generates different types of SMT queries for dependency analysis.
- Writes the generated SMT-LIB v2 query to an output file.

## Usage

```sh
python3 tools/generate_smt.py -i <input_pseudocode_file> -o <output_smt_file> [--query-type <query_type>]
```

### Arguments

-   `-i, --input`: (Required) The path to the input file containing pseudocode.
-   `-o, --output`: (Required) The path to the output file where the SMT-LIB query will be written.
-   `-q, --query-type`: (Optional) The type of SMT query to generate.
    -   `exists_data_forall_bounds_forall_its` (default): Proves Data-Oblivious Full Sequentiality (DOFS) with symbolic loop bounds.
    -   `exists_data_forall_iter_isdep`: Proves DOFS.
    -   `exists_data_exists_bounds_exists_iter_isdep`: Checks for any dependency.
    -   `exists_data_forall_iter_isindep`: Proves Data-Oblivious Full Independence (DOFI).
    -   `exists_data_forall_bounds_forall_iter_isindep`: Proves DOFI with symbolic loop bounds.
    -   `forall_data_forall_bounds_forall_iter_isindep`: Proves universal DOFI.

## Example Usage

To generate an SMT query for data-oblivious full independence (default query type) from `my_pseudocode.pcode` and save it to `output.smt2`:

```sh
python3 tools/generate_smt.py -i my_pseudocode.pcode -o output.smt2
```

To generate a specific query type, e.g., `exists_data_forall_iter_isdep`:

```sh
python3 tools/generate_smt.py -i my_pseudocode.pcode -o output.smt2 --query-type exists_data_forall_iter_isdep
```

## Dependencies

This tool relies on the `pysmt` library and the underlying SMT solver (e.g., Z3). Ensure your environment is set up with these dependencies as specified in `requirements.txt`.

# Demo Pseudocode Files

The `tools/demo/` directory contains several pseudocode examples (`.pcode` files) that can be used with the `generate_smt.py` tool. These examples showcase different types of loop structures and data access patterns relevant to dependency analysis.

-   `sequential_loop.pcode`: A simple loop with a Read-After-Write (RAW) dependency, demonstrating inherent sequentiality.
-   `parallel_loop.pcode`: A simple loop with no inter-iteration dependencies, demonstrating parallelizability.
-   `data_aware_bi.pcode`: A loop with conditional execution, where dependencies depend on data values.
-   `nested_loop_outer_dofs.pcode`: A nested loop where the outer loop exhibits Data-Oblivious Full Sequentiality (DOFS).
-   `indirect_write_scatter.pcode`: A loop with indirect array access for writes (scatter operation), often leading to potential Write-After-Write (WAW) dependencies.