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
│   └── smt.py         # SMT query generation logic and interaction with the SMT solver.
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
- Z3 SMT Solver (required for SMT-based verification)

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
3.  **Install SMT Solver (Z3):**
    P3G relies on an SMT solver, typically Z3. You can install it via `pysmt-install`:
    ```bash
    pysmt-install --z3
    ```

## Running Tests

This project uses `pytest` for testing. The test suite is located in the `tests/cases/` directory.

To run all test cases, execute the following command from the project root:
```bash
pytest
```

## Test Cases

The test suite covers a range of loop structures to verify the correctness of the dependency analysis. Each test case describes a specific loop pattern, its expected parallelization property (Data-Oblivious Full Sequentiality - DOFS, or Not DOFS/Parallelizable), and the reasoning behind it.

### Basic Loops
- **`test_parallel_loop.py`**:
  - **Loop Logic**:
  ```
  for i in 0:n:
    A[i] = B[i] + C[i]
  ```
  - **Description**: Each iteration is independent, reading from `B` and `C` and writing to `A` at the current index `i`. No dependencies between adjacent iterations force sequential execution.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.
- **`test_sequential_loop.py`**:
  - **Loop Logic**:
  ```
  for i = 2...N:
    A[i] = A[i-1] + B[i]
  ```
  - **Description**: This loop has a Read-After-Write (RAW) dependency where `A[i]` reads `A[i-1]`, which was written in the previous iteration. This dependency exists for all iterations.
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.

### Complex Access Patterns
- **`test_array_reversal.py`**:
  - **Loop Logic**:
  ```
  for i = 0...N-1:
    swap(A[i], A[N-1-i])
  ```
  - **Description**: For `N=2`, `A[0]` and `A[1]` are swapped, creating a dependency. If `N` is symbolic, the solver can pick `N=2`, making it sequential. When `N >= 3`, indices `k` and `N-1-k` are distinct and do not overlap with `k+1` and `N-1-(k+1)`, making it parallelizable.
  - **Expected Outcome**: DOFS (Sequential) for general `N` (SMT SAT); Not DOFS (Parallel) for `N >= 3` (SMT UNSAT).
- **`test_long_distance_dependency.py`**:
  - **Loop Logic**:
  ```
  for i = 2...N:
    A[i] = A[max(i-10, 0)] + B[i]
  ```
  - **Description**: `A[i]` depends on `A[max(i-10, 0)]`, a value far removed from `A[i-1]`. No inherent data dependency between *adjacent* iterations forces sequential execution.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.
- **`test_indirect_read_gather.py`**:
  - **Loop Logic**:
  ```
  for i = 1...N:
    A[i] = B[ IDX[i] ]
  ```
  - **Description**: Writes to `A[i]` are independent of previous `A` values, and reads from `B` are indirect. No inherent data dependency between adjacent iterations forces sequential execution.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.
- **`test_indirect_write_scatter.py`**:
  - **Loop Logic**:
  ```
  for i = 1...N:
    A[ IDX[i] ] = B[i]
  ```
  - **Description**: Multiple iterations can write to the same memory location in `A` if `IDX[i]` values are not unique, creating dependencies (e.g., WAW if `IDX[i]=5` for all `i`). The test proves *existence* of a sequentializing data configuration.
  - **Expected Outcome**: Not DOFS (Parallelizable) for *some* data configurations (SMT UNSAT).

### Data-Dependent Analysis
- **`test_data_aware_bi.py`**:
  - **Loop Logic**:
  ```
  for i = 1...N:
    if (B[i] > 0):
      A[i] = A[i-1]
  ```
  - **Description**: If all `B[i] > 0`, then `A[i] = A[i-1]` always executes, creating a sequential dependency.
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.
- **`test_data_aware_bi_b13.py`**:
  - **Loop Logic**:
  ```
  for i = 1...N:
    if (B[i] - B[13] > 0):
      A[i] = A[i-1]
  ```
  - **Description**: If `B[i]=1` and `B[13]=0`, the condition `B[i] - B[13] > 0` is always true, making the loop sequential. However, if `N >= 15`, the loop includes `k=13`, where `B[13] - B[13] > 0` is false, skipping the dependency and making it parallelizable.
  - **Expected Outcome**: DOFS (Sequential) for general `N` (SMT SAT); Not DOFS (Parallel) for `N >= 15` (SMT UNSAT).
- **`test_sequential_with_symbolic_max_index.py`**:
  - **Loop Logic**:
  ```
  for i = 2...N:
    A[i] = A[max(i-w, 0)] + B[i]
  ```
  (where `w` is symbolic)
  - **Description**: Since `w` is symbolic, the SMT solver can choose `w=1`, making the loop `A[i] = A[i-1] + B[i]` (sequential). Thus, a data configuration exists that forces sequentiality.
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.

### Other Cases
- **`test_non_linear_predicate.py`**:
  - **Loop Logic**:
  ```
  for i=0:N:
    if i*i <= N:
      A[i] = B[i] + C[i]  // Parallel part
    else:
      A[i] = A[i-1] + C[i] // Sequential part
  ```
  - **Description**: Because the parallel branch (`A[i] = B[i] + C[i]`) can always be taken for some `k` (e.g., for `k=0`, `0*0 <= N` is always true for `N >= 0`), there is no data configuration that forces *all* adjacent iterations to be sequential.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.
- **`test_nested_loop.py`**:
  - **Loop Logic**:
  ```
  for i = 1...N:
    for j = 1...M:
      A[i, j] = A[i-1, j] + B[i, j]
  ```
  - **Description**: The outer loop (over `i`) has a true data dependency (`A[i,j]` depends on `A[i-1,j]`), making it DOFS. The inner loop (over `j`) has no self-dependency, making it Not DOFS (parallelizable).
  - **Expected Outcome**: Outer Loop DOFS (Sequential); Inner Loop Not DOFS (Parallel).
- **`test_cholesky.py`**:
  - **Loop Logic**:
    ```
    // Simplified Cholesky
    for i = 2...N:
      for j = 2...i:
        L[i, j] = L[i, j-1] + L[j-1, j-1]

    // Full Cholesky Kernel (simplified for P3G modeling)
    for i = 0 to N-1:
      for j = 0 to i:
        sum_val = 0
        for k = 0 to j-1:
          sum_val = sum_val + L[i,k] * L[j,k]
        L[i,j] = A[i,j] - sum_val
    ```
  - **Description**: The simplified inner loop has a dependency `L[i,j] <- L[i,j-1]`, making it DOFS. The simplified outer loop is Not DOFS. The full Cholesky kernel is highly sequential due to dependencies across all three nested loops.
  - **Expected Outcome**: Simplified Inner Loop DOFS (Sequential); Simplified Outer Loop Not DOFS (Parallel); Full Cholesky Kernel DOFS (Sequential).
- **`test_gauss_seidel.py`**:
  - **Loop Logic**:
    ```
    // Red Pass (odd indices)
    for i = 1, 3, 5, ...:
      A[i] = A[i-1] + A[i+1]

    // Black Pass (even indices)
    for i = 2, 4, 6, ...:
      A[i] = A[i-1] + A[i+1]

    // Traditional 1D Gauss-Seidel
    for i = 1 to N-1:
      A[i] = A[i-1] + A[i+1]
    ```
  - **Description**: Both Red and Black passes involve writes to odd/even indices and reads from adjacent even/odd indices, respectively. No dependency between iterations for any data configuration, making them parallel. The Traditional 1D Gauss-Seidel loop is inherently sequential due to a Read-After-Write (RAW) dependency where `A[i]` depends on `A[i-1]` from the current iteration.
  - **Expected Outcome**: Both Red and Black Passes Not DOFS (Parallelizable). SMT query returns UNSAT. Traditional 1D Gauss-Seidel DOFS (Sequential). SMT query returns SAT.