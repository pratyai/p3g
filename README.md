# P3G : Loop Analysis Tool

## Overview

P3G is a prototype tool for analyzing loops in a simple imperative language to determine their potential for parallelization. It represents loop structures using a graph-based intermediate representation (P3G) and uses an SMT solver (like Z3) to formally verify the presence or absence of data dependencies.

The primary analysis performed is for **Data-Oblivious Full Sequentiality (DOFS)**. A loop is considered sequential from a DOFS perspective if a data dependency is proven to exist between adjacent iterations for all possible data inputs. If a counterexample can be found (i.e., a scenario where no dependency exists between adjacent iterations), the loop is considered "not fully sequential" and a candidate for parallelization.

## Features

- **Graph-based Representation**: Models loop nests, branches, and computations as a P3G.
- **SMT-based Verification**: Generates SMT-LIB queries to formally prove or disprove data dependencies.
- **Data-Oblivious Analysis**: Analyzes loops for parallelism independent of the actual data values.
- **Support for Complex Scenarios**: Includes test cases for various complex loop structures, including:
    - Indirect and symbolic array accesses.
    - Data-dependent and non-linear predicates.
    - Nested loops.

## Project Structure

```
.
├── p3g/
│   ├── __init__.py
│   ├── p3g.py         # Core P3G graph-building components.
│   └── smt.py         # SMT query generation logic.
├── tests/
│   ├── cases/         # Individual test cases for different loop types.
│   └── test_utils.py  # Helper functions for tests.
├── .gitignore
├── pyproject.toml
└── requirements.txt
```

## Getting Started

### Prerequisites

- Python 3.9+

### Installation

1.  **Clone the repository:**
    ```bash
    git clone <repository-url>
    cd p3g
    ```

2.  **Install dependencies:**
    It is recommended to use a virtual environment.
    ```bash
    python -m venv .venv
    source .venv/bin/activate
    pip install -r requirements.txt
    ```

## Running Tests

This project uses `pytest` for testing. The test suite is located in the `tests/cases/` directory.

To run all test cases, execute the following command from the project root:
```bash
pytest
```

## Test Cases

The test suite covers a range of loop structures to verify the correctness of the dependency analysis.

### Basic Loops
- **`test_parallel_loop.py`**: A simple parallel loop with no dependencies (`A[i] = B[i] + C[i]`).
- **`test_sequential_loop.py`**: A simple sequential loop with a dependency on the previous iteration (`A[i] = A[i-1] + B[i]`).

### Complex Access Patterns
- **`test_array_reversal.py`**: An array reversal loop (`swap(A[i], A[N-1-i])`).
- **`test_long_distance_dependency.py`**: A loop with a dependency on a distant previous iteration (`A[i] = A[max(i-10, 0)] + B[i]`).
- **`test_indirect_read_gather.py`**: A parallel loop with an indirect read (`A[i] = B[IDX[i]]`).
- **`test_indirect_write_scatter.py`**: A sequential loop with an indirect write (`A[IDX[i]] = B[i]`).

### Data-Dependent Analysis
- **`test_data_aware_bi.py`**: A loop where the dependency is conditioned on a data-dependent branch.
- **`test_data_aware_bi_b13.py`**: A loop with a more complex data-dependent predicate.
- **`test_sequential_with_symbolic_max_index.py`**: A loop with a symbolic dependency distance (`A[i] = A[max(i-w, 0)]`).

### Other Cases
- **`test_non_linear_predicate.py`**: A loop with a non-linear predicate in a branch.
- **`test_nested_loop.py`**: A nested loop with a sequential outer loop and a parallel inner loop.