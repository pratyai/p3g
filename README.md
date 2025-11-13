# P3G : Loop Analysis Tool

## Overview

P3G is a prototype tool for analyzing loops in a simple imperative language to determine their potential for parallelization. It represents loop structures using a graph-based intermediate representation (P3G) and uses an SMT solver (like Z3) to formally verify the presence or absence of data dependencies.

The primary analysis performed is for **Data-Oblivious Full Sequentiality (DOFS)**. A loop is considered sequential from a DOFS perspective if a data dependency is proven to exist between adjacent iterations for all possible data inputs. If the SMT query is unsatisfiable (UNSAT), it proves that for any data configuration, at least one pair of adjacent iterations remains independent, making the loop "not fully sequential" and a candidate for parallelization.

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

1. **Clone the repository:**
    ```bash
    git clone <repository-url>
    cd p3g
    ```

1. **Install dependencies:**
    It is recommended to use a virtual environment.
    ```bash
    python -m venv .venv
    source .venv/bin/activate
    pip install -r requirements.txt
    ```

1. **Install SMT Solver (Z3):**
    P3G relies on an SMT solver, typically Z3. You can install it via `pysmt-install` :
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

#### `test_parallel_loop.py`

- **Loop Logic**:
  ```
  for i in 0:n:
    A[i] = B[i] + C[i]
  ```

- **Description**: This loop is inherently parallelizable as each iteration is independent, reading from `B` and `C` and writing to `A` at the current index `i` . There are no dependencies between adjacent iterations that would force sequential execution.
  - `test_parallel_loop_dofs` :
    - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
  - `test_parallel_loop_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_parallel_loop_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### `test_sequential_loop.py`

- **Loop Logic**:
  ```
  for i = 2...N:
    A[i] = A[i-1] + B[i]
  ```

- **Description**: This loop has a Read-After-Write (RAW) dependency where `A[i]` reads `A[i-1]` , which was written in the previous iteration. This dependency exists for all iterations, making the loop inherently sequential.
  - `test_sequential_loop_dofs` :
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
  - `test_sequential_loop_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_sequential_loop_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

### Complex Access Patterns

#### `test_array_reversal.py`

- **Loop Logic**:
    ```
    for i = 0...N-1:
      swap(A[i], A[N-1-i])
    ```

- **Description**: This loop swaps elements `A[i]` and `A[N-1-i]` . The parallelizability depends on the value of `N` .
  - `test_array_reversal_dofs` :
    - **Description**: Tests the general case. For `N=2` , `A[0]` and `A[1]` are swapped, creating a dependency. If `N` is symbolic, the solver can pick `N=2` , making it sequential.
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
  - `test_array_reversal_high_N_dofs` :
    - **Description**: Tests the case where `N >= 3` . When `N >= 3` , indices `k` and `N-1-k` are distinct and do not overlap with `k+1` and `N-1-(k+1)` , making it parallelizable.
    - **Expected Outcome**: Not DOFS (Parallel). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
  - `test_array_reversal_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_array_reversal_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

#### `test_long_distance_dependency.py`

- **Loop Logic**:
  ```
  for i = 2...N:
    A[i] = A[max(i-10, 0)] + B[i]
  ```

- **Description**: `A[i]` depends on `A[max(i-10, 0)]` , a value far removed from `A[i-1]` . This means there is no inherent data dependency between *adjacent* iterations that would force sequential execution.
  - `test_long_distance_dependency_dofs` :
    - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
  - `test_long_distance_dependency_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_long_distance_dependency_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### `test_indirect_read_gather.py`

- **Loop Logic**:
  ```
  for i = 1...N:
    A[i] = B[ IDX[i] ]
  ```

- **Description**: This operation is generally parallelizable because writes to `A[i]` are independent of previous `A` values, and reads from `B` are indirect. There is no inherent data dependency between adjacent iterations that would force sequential execution for all data configurations.
  - `test_indirect_read_gather_dofs` :
    - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
  - `test_indirect_read_gather_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_indirect_read_gather_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### `test_indirect_write_scatter.py`

- **Loop Logic**:
  ```
  for i = 1...N:
    A[ IDX[i] ] = B[i]
  ```

- **Description**: This operation is generally sequential because multiple iterations can write to the same memory location in `A` if `IDX[i]` values are not unique or create dependencies (e.g., WAW if `IDX[i]=5` for all `i` ). The test proves *existence* of a sequentializing data configuration.
  - `test_indirect_write_scatter_dofs` :
    - **Expected Outcome**: Not DOFS (Parallelizable) for *some* data configurations. SMT query returns UNSAT, proving that no data configuration forces sequentiality across *all* adjacent iterations.
  - `test_indirect_write_scatter_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_indirect_write_scatter_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: Not DOFS (Parallelizable) for *some* data configurations. SMT query returns UNSAT, proving that no data configuration forces sequentiality across *all* adjacent iterations.

#### `test_non_linear_access.py` / `test_non_linear_access_dofs`

- **Loop Logic**:
  ```
  for i=0:N:
    A[i*i] = B[i] + C[i]
  ```

- **Description**: This loop involves a non-linear array access pattern (`A[i*i]`). Due to the quadratic growth of the index, for `i > 0`, `i*i` and `(i+1)*(i+1)` are distinct and sufficiently far apart. This prevents adjacent iteration dependencies, making the loop parallelizable.
  - `test_non_linear_access_dofs` :
    - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
  - `test_non_linear_access_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_non_linear_access_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### `test_non_linear_access.py` / `test_non_linear_access_sequential_dofs`

- **Loop Logic**:
  ```
  for i = 1...N:
    A[i*i] = A[(i-1)*(i-1)] + B[i]
  ```

- **Description**: This loop involves a non-linear array access pattern (`A[i*i]`) that introduces a Read-After-Write (RAW) dependency. `A[i*i]` reads a value written to `A[(i-1)*(i-1)]` in the previous iteration. This dependency exists for all iterations, making the loop inherently sequential.
  - `test_non_linear_access_sequential_dofs` :
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
  - `test_non_linear_access_sequential_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_non_linear_access_sequential_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

### Data-Dependent Analysis

#### `test_data_aware_bi.py`

- **Loop Logic**:
  ```
  for i = 1...N:
    if (B[i] > 0):
      A[i] = A[i-1]
  ```

- **Description**: This loop's dependency is conditional on the data in `B` . If all `B[i] > 0` , then `A[i] = A[i-1]` always executes, creating a sequential dependency.
  - `test_data_aware_bi_dofs` :
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
  - `test_data_aware_bi_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_data_aware_bi_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

#### `test_data_aware_bi_b13.py`

- **Loop Logic**:
  ```
  for i = 1...N:
    if (B[i] - B[13] > 0):
      A[i] = A[i-1]
  ```

- **Description**: This loop's dependency is conditional on the difference between `B[i]` and a constant `B[13]` .
  - `test_data_aware_bi_b13_dofs` :
    - **Description**: Tests the general case. If `B[i]=1` and `B[13]=0` , the condition `B[i] - B[13] > 0` is always true, making the loop sequential.
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
  - `test_data_aware_bi_b13_high_N_dofs` :
    - **Description**: Tests the case where `N >= 15` . If `N >= 15` , the loop includes `k=13` , where `B[13] - B[13] > 0` is false, skipping the dependency and making it parallelizable.
    - **Expected Outcome**: Not DOFS (Parallel). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
  - `test_data_aware_bi_b13_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_data_aware_bi_b13_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

#### `test_sequential_with_symbolic_max_index.py`

- **Loop Logic**:
  ```
  for i = 2...N:
    A[i] = A[max(i-w, 0)] + B[i]
  ```
  (where `w` is symbolic)

- **Description**: This loop's dependency involves a symbolic variable `w` in the `max` function. Since `w` is symbolic, the SMT solver can choose `w=1` , making the loop `A[i] = A[i-1] + B[i]` (sequential). Thus, a data configuration exists that forces sequentiality.
  - `test_sequential_with_symbolic_max_index_dofs` :
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
  - `test_sequential_with_symbolic_max_index_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_sequential_with_symbolic_max_index_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

### Other Cases

#### `test_non_linear_predicate.py`

- **Loop Logic**:
  ```
  for i=0:N:
    if i*i <= N:
      A[i] = B[i] + C[i]  // Parallel part
    else:
      A[i] = A[i-1] + C[i] // Sequential part
  ```

- **Description**: This loop contains a non-linear predicate ( `i*i <= N` ) that determines whether a parallel or sequential branch is taken. Because the parallel branch ( `A[i] = B[i] + C[i]` ) can always be taken for some `k` (e.g., for `k=0` , `0*0 <= N` is always true for `N >= 0` ), there is no data configuration that forces *all* adjacent iterations to be sequential.
  - `test_non_linear_predicate_dofs` :
    - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
  - `test_non_linear_predicate_dofs_forall_bounds` :
    - **Description**: Analyzes the same loop logic as `test_non_linear_predicate_dofs` , but using loop bounds SMT generation.
    - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### `test_nested_loop.py` / `test_nested_loop_outer_dofs`

- **Loop Logic**:
  ```
  for i = 1...N:
    for j = 1...M:
      A[i, j] = A[i-1, j] + B[i, j]
  ```

- **Description**: The outer loop (over `i` ) has a true data dependency ( `A[i,j]` depends on `A[i-1,j]` ), making it DOFS. The inner loop (over `j` ) has no self-dependency, making it Not DOFS (parallelizable).
- `test_nested_loop_outer_dofs_dofs` :
  - **Expected Outcome**: Outer Loop DOFS (Sequential); Inner Loop Not DOFS (Parallel). SMT query returns SAT for the outer loop, UNSAT for the inner loop.
- `test_nested_loop_outer_dofs_forall_bounds` :
  - **Description**: Analyzes the same loop logic as `test_nested_loop_outer_dofs_dofs` , but using loop bounds SMT generation.
  - **Expected Outcome**: Outer Loop DOFS (Sequential); Inner Loop Not DOFS (Parallel). SMT query returns SAT for the outer loop, UNSAT for the inner loop.

#### `test_nested_loop.py` / `test_nested_loop_inner_dofs`

- **Loop Logic**:
  ```
  for i = 1...N:
    for j = 1...M:
      A[i, j] = A[i, j-1] + B[i, j]
  ```

- **Description**: The outer loop (over `i` ) has no self-dependency, making it Not DOFS (parallelizable). The inner loop (over `j` ) has a true data dependency ( `A[i,j]` depends on `A[i,j-1]` ), making it DOFS.
- `test_nested_loop_inner_dofs_dofs` :
  - **Expected Outcome**: Outer Loop Not DOFS (Parallel); Inner Loop DOFS (Sequential). SMT query returns UNSAT for the outer loop, SAT for the inner loop.
- `test_nested_loop_inner_dofs_forall_bounds` :
  - **Description**: Analyzes the same loop logic as `test_nested_loop_inner_dofs_dofs` , but using loop bounds SMT generation.
  - **Expected Outcome**: Outer Loop Not DOFS (Parallel); Inner Loop DOFS (Sequential). SMT query returns UNSAT for the outer loop, SAT for the inner loop.

#### `test_cholesky.py` / `test_cholesky_sequential`

- **Loop Logic**:
  ```
  // Simplified Cholesky
  for i = 2...N:
    for j = 2...i:
      L[i, j] = L[i, j-1] + L[j-1, j-1]
  ```

- **Description**: This test models a simplified dependency pattern. It analyzes both the inner and outer loops of this simplified kernel. The inner loop has a true data dependency, making it DOFS. The outer loop has no self-dependency, making it Not DOFS (parallelizable).
- `test_cholesky_sequential_inner_dofs` :
  - **Expected Outcome**: Inner Loop DOFS (Sequential). SMT query returns SAT.
- `test_cholesky_sequential_outer_dofs` :
  - **Expected Outcome**: Outer Loop Not DOFS (Parallel). SMT query returns UNSAT.
- `test_cholesky_sequential_inner_dofs_forall_bounds` :
  - **Description**: Analyzes the inner loop logic, but using loop bounds SMT generation.
  - **Expected Outcome**: Inner Loop DOFS (Sequential). SMT query returns SAT.
- `test_cholesky_sequential_outer_dofs_forall_bounds` :
  - **Description**: Analyzes the outer loop logic, but using loop bounds SMT generation.
  - **Expected Outcome**: Outer Loop Not DOFS (Parallel). SMT query returns UNSAT.

#### `test_cholesky.py` / `test_cholesky_full_kernel`

- **Loop Logic**:
  ```
  // Full Cholesky Kernel (simplified for P3G modeling)
  for i = 0 to N-1:
    for j = 0 to i:
      sum_val = 0
      for k = 0 to j-1:
        sum_val = sum_val + L[i,k] * L[j,k]
      L[i,j] = A[i,j] - sum_val
  ```

- **Description**: This test models a more accurate Cholesky Decomposition kernel. It is highly sequential due to dependencies across all three nested loops.
- `test_cholesky_full_kernel_dofs` :
  - **Expected Outcome**: Full Cholesky Kernel DOFS (Sequential). SMT query returns SAT.
- `test_cholesky_full_kernel_dofs_forall_bounds` :
  - **Description**: Analyzes the same loop logic as `test_cholesky_full_kernel_dofs` , but using loop bounds SMT generation.
  - **Expected Outcome**: Full Cholesky Kernel DOFS (Sequential). SMT query returns SAT.

#### `test_gauss_seidel.py` / `test_gauss_seidel_red`

- **Loop Logic**:
  ```
  // Red Pass (odd indices)
  for i = 1, 3, 5, ...:
    A[i] = A[i-1] + A[i+1]
  ```

- **Description**: This test covers the Red pass of Gauss-Seidel. It involves writes to odd indices and reads from adjacent even indices. No dependency between iterations for any data configuration, making it parallel.
- `test_gauss_seidel_red_dofs` :
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
- `test_gauss_seidel_red_dofs_forall_bounds` :
  - **Description**: Analyzes the same loop logic as `test_gauss_seidel_red_dofs` , but using loop bounds SMT generation.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### `test_gauss_seidel.py` / `test_gauss_seidel_black`

- **Loop Logic**:
  ```
  // Black Pass (even indices)
  for i = 2, 4, 6, ...:
    A[i] = A[i-1] + A[i+1]
  ```

- **Description**: This test covers the Black pass of Gauss-Seidel. It involves writes to even indices and reads from adjacent odd indices. No dependency between iterations for any data configuration, making it parallel.
- `test_gauss_seidel_black_dofs` :
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
- `test_gauss_seidel_black_dofs_forall_bounds` :
  - **Description**: Analyzes the same loop logic as `test_gauss_seidel_black_dofs` , but using loop bounds SMT generation.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### `test_gauss_seidel.py` / `test_gauss_seidel_traditional`

- **Loop Logic**:
  ```
  // Traditional 1D Gauss-Seidel
  for i = 1 to N-1:
    A[i] = A[i-1] + A[i+1]
  ```

- **Description**: This loop is inherently sequential due to a Read-After-Write (RAW) dependency where `A[i]` depends on `A[i-1]` from the current iteration.
- `test_gauss_seidel_traditional_dofs` :
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
- `test_gauss_seidel_traditional_dofs_forall_bounds` :
  - **Description**: Analyzes the same loop logic as `test_gauss_seidel_traditional_dofs` , but using loop bounds SMT generation.
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
