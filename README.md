# P3G : Loop Analysis Tool

## Overview
P3G is a prototype tool for analyzing loops in simple imperative programs to determine their potential for parallelization. It represents loop structures using a graph-based intermediate representation (P3G) and uses an SMT solver (like Z3) to formally verify the presence or absence of data dependencies across loop iterations.

The tool supports several kinds of formal analysis:
- **Data-Oblivious Full Sequentiality (DOFS)**: A loop is DOFS if there **exists** a data configuration that forces a dependency between **all** adjacent iterations. A `SAT` result for a DOFS query means the loop is sequential under some data pattern. An `UNSAT` result proves the loop is parallelizable because no single data pattern can make it fully sequential.
- **Data-Oblivious Full Independence (DOFI)**: A loop is DOFI if there **exists** a data configuration for which **no** dependencies exist between **any** pair of iterations. A `SAT` result for a DOFI query proves the loop is parallelizable under some data pattern.
- **Dependency Existence**: A relaxed query that checks if there **exists** any data configuration, loop bounds, and iteration pair that can cause a dependency. A `SAT` result proves the loop is not fully parallel.

## Table of Contents
- [Features](#features)
- [Project Structure](#project-structure)
- [Getting Started](#getting-started)
- [Running Tests](#running-tests)
- [Test Cases](#test-cases)
  - [Basic Loops](#basic-loops)
  - [Complex Access Patterns](#complex-access-patterns)
  - [Data-Dependent Analysis](#data-dependent-analysis)
  - [Other Cases](#other-cases)

## Features
- **Graph-based Representation**: Models loop nests (`Loop`), parallel maps (`Map`), reductions (`Reduce`), and conditional logic (`Branch`) as a P3G.
- **Multi-dimensional Data Access**: Supports multi-dimensional array accesses using `PysmtCoordSet` and `PysmtRange`.
- **SMT-based Verification**: Generates SMT-LIB queries for different formal analyses (DOFS, DOFI, dependency existence).
- **Support for Complex Scenarios**: Includes a rich test suite for various complex loop structures, including:
    - Indirect and symbolic array accesses.
    - Data-dependent and non-linear predicates.
    - Nested loops.

## Project Structure

```
.
├── p3g/
│   ├── p3g.py         # Core P3G graph-building components.
│   └── smt.py         # SMT query generation logic.
├── tests/
│   ├── cases/         # Individual test cases for different loop types.
│   └── test_utils.py  # Helper functions for tests.
├── tools/
│   └── simplify.py    # A utility to simplify SMT-LIB files.
├── .gitignore
├── pyproject.toml
├── requirements.txt
└── README.md
```

## Getting Started

### Prerequisites
- Python 3.9+
- Z3 SMT Solver

### Installation
1. **Clone the repository:**
    ```bash
    git clone <repository-url>
    cd p3g
    ```
2. **Install dependencies:**
    It is recommended to use a virtual environment.
    ```bash
    python -m venv .venv
    source .venv/bin/activate
    pip install -r requirements.txt
    ```
3. **Install SMT Solver (Z3):**
    P3G relies on Z3. The required `z3-solver` Python package is included in `requirements.txt` and will be installed automatically.

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

- **Description**: This loop is inherently parallelizable as each iteration is independent. Each iteration `i` only reads from `B[i]` and `C[i]` and writes to `A[i]`. There are no dependencies between adjacent iterations that would force sequential execution.

- `test_dofs`:
  - **Description**: Checks for Data-Oblivious Full Sequentiality (DOFS).
  - **Expected Outcome**: Not DOFS (Parallelizable). The SMT query returns UNSAT, proving that no data configuration can make this loop fully sequential.

- `test_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.

- `test_dofi`:
  - **Description**: Checks for Data-Oblivious Full Independence (DOFI).
  - **Expected Outcome**: DOFI (Parallelizable). The SMT query returns SAT, proving that a data configuration exists (which is all configurations in this case) that makes the loop fully independent.

- `test_dofi_forall_bounds`:
  - **Description**: Analyzes DOFI with universally quantified loop bounds.
  - **Expected Outcome**: DOFI (Parallelizable). SMT query returns SAT.

- `test_forall_data_forall_bounds`:
  - **Description**: Checks if the loop is independent for *all* data configurations.
  - **Expected Outcome**: DOFI for all data (Always Parallel). The SMT query returns SAT, proving the loop is parallel regardless of the contents of `B` and `C`.

- `test_find_dependency`:
  - **Description**: Uses a relaxed check to find if *any* dependency can exist.
  - **Expected Outcome**: No dependency. The SMT query returns UNSAT.

#### `test_sequential_loop.py`

- **Loop Logic**:
  ```
  for i = 2...N:
    A[i] = A[i-1] + B[i]
  ```

- **Description**: This is a classic sequential loop due to a Read-After-Write (RAW) dependency: `A[i]` reads `A[i-1]`, which was written in the previous iteration. This dependency exists for all iterations in the loop range.

- `test_dofs`:
  - **Description**: Checks for Data-Oblivious Full Sequentiality (DOFS).
  - **Expected Outcome**: DOFS (Sequential). The SMT query returns SAT, proving that a data configuration exists (which is inherent in the loop structure) that forces sequential execution.

- `test_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.

- `test_dofi`:
  - **Description**: Checks for Data-Oblivious Full Independence (DOFI).
  - **Expected Outcome**: Not DOFI (Sequential). The SMT query returns UNSAT, as no data configuration can make this loop fully independent.

- `test_dofi_forall_bounds`:
  - **Description**: Analyzes DOFI with universally quantified loop bounds.
  - **Expected Outcome**: Not DOFI (Sequential). SMT query returns UNSAT.

- `test_forall_data_forall_bounds`:
  - **Description**: Checks if the loop is independent for *all* data configurations.
  - **Expected Outcome**: Not DOFI for all data (Always Sequential). The SMT query returns UNSAT, as the loop is inherently sequential.

- `test_find_dependency`:
  - **Description**: Uses a relaxed check to find if *any* dependency can exist.
  - **Expected Outcome**: Dependency exists. The SMT query returns SAT, as the RAW dependency is always present.

### Complex Access Patterns

#### `test_array_reversal.py`

- **Loop Logic**:
  ```
  for i = 0...N-1:
    swap(A[i], A[N-1-i])
  ```

- **Description**: This loop swaps elements from opposite ends of an array. The parallelizability of this loop is highly dependent on the value of `N` (the array size). For small `N`, dependencies can exist between adjacent iterations.

- `test_dofs`:
  - **Description**: Checks for Data-Oblivious Full Sequentiality (DOFS).
  - **Expected Outcome**: DOFS (Sequential). The SMT query returns SAT. The solver can find a value for `N` (e.g., `N=2`) where `swap(A[0], A[1])` and `swap(A[1], A[0])` create a dependency between adjacent iterations.

- `test_high_N_dofs`:
  - **Description**: Checks for DOFS with the additional constraint that `N >= 3`.
  - **Expected Outcome**: Not DOFS (Parallelizable). The SMT query returns UNSAT. When `N >= 3`, for any iteration `k`, the indices `k` and `N-1-k` are distinct and do not overlap with the indices for the next iteration `k+1`. This means no data configuration can force sequential execution across all adjacent iterations.

- `test_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: Not DOFS (Parallelizable). The SMT query returns UNSAT. Because the solver must consider all possible loop bounds, it will encounter cases where `N >= 3`, which breaks the dependency chain for adjacent iterations.

- `test_find_dependency`:
  - **Description**: Uses a relaxed check to find if *any* dependency can exist between *any* two iterations `j < k`.
  - **Expected Outcome**: Dependency exists. The SMT query returns SAT. The solver can find a data configuration for `N` (e.g., `N=2`) that creates a dependency.

#### `test_long_distance_dependency.py`

- **Loop Logic**:
  ```
  for i = 2...N:
    A[i] = A[max(i-10, 0)] + B[i]
  ```

- **Description**: This test analyzes a loop where the dependency `A[i] <- A[max(i-10, 0)]` has a fixed, long distance (10 iterations). The DOFS analysis, which checks for dependencies between adjacent iterations (`k` and `k+1`), should not find a dependency.

- `test_dofs`:
  - **Description**: Checks for Data-Oblivious Full Sequentiality (DOFS) between adjacent iterations.
  - **Expected Outcome**: Not DOFS (Parallel). The SMT query returns UNSAT because the dependency distance is greater than 1.

- `test_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: Not DOFS (Parallel). SMT query returns UNSAT.

- `test_find_dependency`:
  - **Description**: Uses a relaxed check to find if *any* dependency exists between *any* two iterations `j < k`.
  - **Expected Outcome**: Dependency exists. The SMT query returns SAT because this relaxed query is able to find the long-distance dependency (e.g., between iteration `k=2` and `k=12`).

#### `test_indirect_read_gather.py`

- **Loop Logic**:
  ```
  for i = 1...N:
    A[i] = B[ IDX[i] ]
  ```

- **Description**: This "gather" operation reads from an array `B` using an indirect index from array `IDX` and writes to a sequential index `i` in array `A`. Since each iteration `i` writes to a unique location `A[i]`, there are no write-related dependencies (WAW, WAR). Reads from `B` do not create dependencies between iterations. Therefore, the loop is fully parallel.

- `test_dofs`:
  - **Description**: Checks for Data-Oblivious Full Sequentiality (DOFS).
  - **Expected Outcome**: Not DOFS (Parallelizable). The SMT query returns UNSAT. No data configuration for `IDX` can force a dependency.

- `test_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.

- `test_dofi`:
  - **Description**: Checks for Data-Oblivious Full Independence (DOFI).
  - **Expected Outcome**: DOFI (Parallelizable). The SMT query returns SAT. A parallelizing data configuration for `IDX` can always be found (in fact, all configurations are parallel).

- `test_dofi_forall_bounds`:
  - **Description**: Analyzes DOFI with universally quantified loop bounds.
  - **Expected Outcome**: DOFI (Parallelizable). SMT query returns SAT.

- `test_forall_data_forall_bounds`:
  - **Description**: Checks if the loop is independent for *all* data configurations.
  - **Expected Outcome**: DOFI for all data (Always Parallel). The SMT query returns SAT, proving the loop is parallel regardless of the contents of `IDX`.

- `test_find_dependency`:
  - **Description**: Uses a relaxed check to find if *any* dependency can exist.
  - **Expected Outcome**: No dependency. The SMT query returns UNSAT.

#### `test_indirect_write_scatter.py`

- **Loop Logic**:
  ```
  for i = 1...N:
    A[ IDX[i] ] = B[i]
  ```

- **Description**: This "scatter" operation writes to an array `A` using an indirect index from array `IDX`. A Write-After-Write (WAW) dependency can exist if different iterations write to the same location (i.e., if `IDX[j] == IDX[k]` for `j != k`).

- `test_dofs`:
  - **Description**: Checks for Data-Oblivious Full Sequentiality (DOFS).
  - **Expected Outcome**: DOFS (Sequential). The SMT query returns SAT. The solver can find a data configuration for the `IDX` array (e.g., `IDX[i] = 0` for all `i`) that forces a dependency between all adjacent iterations.

- `test_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.

- `test_dofi`:
  - **Description**: Checks for Data-Oblivious Full Independence (DOFI).
  - **Expected Outcome**: DOFI (Parallelizable). The SMT query returns SAT. The solver can find a data configuration for `IDX` (e.g., `IDX[i] = i`) that avoids all dependencies, making the loop fully parallel.

- `test_dofi_forall_bounds`:
  - **Description**: Analyzes DOFI with universally quantified loop bounds.
  - **Expected Outcome**: DOFI (Parallelizable). SMT query returns SAT.

- `test_forall_data_forall_bounds`:
  - **Description**: Checks if the loop is independent for *all* data configurations.
  - **Expected Outcome**: Not DOFI for all data (Sequential case exists). The SMT query returns UNSAT, because a conflicting `IDX` array can always be constructed.

- `test_find_dependency`:
  - **Description**: Uses a relaxed check to find if *any* dependency can exist.
  - **Expected Outcome**: Dependency exists. The SMT query returns SAT, as the solver can easily find a case where `IDX[j] = IDX[k]`.

#### `test_non_linear_access.py`

- **Description**: Analyzes loops with non-linear (quadratic) array access patterns.

- **Parallel Non-Linear Access**
  - **Loop Logic**:
    ```
    for i=0:N:
      A[i*i] = B[i] + C[i]
  ```

- **Description**: This loop writes to `A` using a quadratic index `i*i`. The distance between access indices for adjacent iterations (`(i+1)^2 - i^2 = 2i+1`) grows, ensuring no dependencies are created.

- `test_dofs`:
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.

- `test_dofs_forall_bounds`:
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.

- `test_find_dependency`:
  - **Expected Outcome**: No dependency. SMT query returns UNSAT.

- **Sequential Non-Linear Access**
  - **Loop Logic**:
    ```
    for i = 1...N:
      A[i*i] = A[(i-1)*(i-1)] + B[i]
  ```

- **Description**: This loop has a Read-After-Write (RAW) dependency where the write to `A[i*i]` depends on the read from `A[(i-1)*(i-1)]`, which was written in the previous iteration.

- `test_sequential_dofs`:
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.

- `test_sequential_dofs_forall_bounds`:
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.

- `test_sequential_find_dependency`:
  - **Expected Outcome**: Dependency exists. SMT query returns SAT.

### Data-Dependent Analysis

#### `test_data_aware_bi.py`

- **Loop Logic**:
  ```
  for i = 1...N:
    if (B[i] > 0):
      A[i] = A[i-1]
  ```

- **Description**: This test case analyzes a loop with a data-dependent conditional branch. A dependency exists only if the condition `B[i] > 0` is met.

- `test_dofs`:
  - **Description**: Checks for Data-Oblivious Full Sequentiality (DOFS).
  - **Expected Outcome**: DOFS (Sequential). The SMT query returns SAT. The solver can find a data configuration (e.g., setting all `B[i]` values to be greater than 0) that makes the sequential branch `A[i] = A[i-1]` execute for all iterations, thus proving a sequential case exists.

- `test_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: DOFS (Sequential). The SMT query returns SAT, as the existence of a sequentializing data configuration is not dependent on the specific loop bounds.

- `test_find_dependency`:
  - **Description**: Uses a relaxed check to find if *any* dependency can exist.
  - **Expected Outcome**: Dependency exists. The SMT query returns SAT, as the solver can easily find a data configuration where the condition is met for at least two consecutive iterations.

#### `test_data_aware_bi_b13.py`

- **Loop Logic**:
  ```
  for i = 1...N:
    if (B[i] - B[13] > 0):
      A[i] = A[i-1]
  ```

- **Description**: This test case features a conditional dependency that references a fixed index (`B[13]`). The analysis must consider how the loop bounds (`N`) interact with this fixed index.

- `test_dofs`:
  - **Description**: Checks for Data-Oblivious Full Sequentiality (DOFS).
  - **Expected Outcome**: DOFS (Sequential). The SMT query returns SAT. The solver can find a data configuration and loop bounds (e.g., `N < 13`) that make the condition `B[i] - B[13] > 0` true for all iterations, thus forcing a sequential dependency.

- `test_high_N_dofs`:
  - **Description**: Checks for DOFS with the additional constraint that `N >= 15`.
  - **Expected Outcome**: Not DOFS (Parallelizable). The SMT query returns UNSAT. When `N >= 15`, the loop is guaranteed to include the iteration `i=13`. At this point, the condition `B[13] - B[13] > 0` is always false, breaking the chain of dependencies.

- `test_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: Not DOFS (Parallelizable). The SMT query returns UNSAT. Because the solver must consider all possible loop bounds, it will encounter cases where `N >= 13`, which breaks the dependency chain, so it cannot prove that a data configuration exists that makes it sequential for *all* possible bounds. *(Note: The test case expects False/UNSAT)*.

- `test_find_dependency`:
  - **Description**: Uses a relaxed check to find if *any* dependency can exist.
  - **Expected Outcome**: Dependency exists. The SMT query returns SAT, as the solver can easily find a data and bounds configuration where the sequential branch is taken for at least two consecutive iterations.

#### `test_sequential_with_symbolic_max_index.py`

- **Loop Logic**:
  ```
  for i = 2...N:
    A[i] = A[max(i-w, 0)] + B[i]
  ```
  (where `w` is a symbolic variable)

- **Description**: This test analyzes a loop with a symbolic dependency distance, `w`. The SMT solver must determine if there *exists* a value for `w` that can force the loop to be sequential.

- `test_dofs`:
  - **Description**: Checks for Data-Oblivious Full Sequentiality (DOFS).
  - **Expected Outcome**: DOFS (Sequential). The SMT query returns SAT. The solver can choose a value for `w` (e.g., `w=1`) that creates a direct Read-After-Write dependency (`A[i]` depends on `A[i-1]`), making the loop sequential.

- `test_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: DOFS (Sequential). The SMT query returns SAT, as the ability to choose `w=1` is independent of the loop bounds.

- `test_find_dependency`:
  - **Description**: Uses a relaxed check to find if *any* dependency can exist.
  - **Expected Outcome**: Dependency exists. The SMT query returns SAT, as the solver can easily find a configuration for `w` that creates a dependency.

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

- **Description**: This test case analyzes a loop where a non-linear predicate (`i*i <= N`) determines whether a parallel or a sequential code path is executed. The analysis must reason about whether the sequential path can be forced for all iterations.

- `test_dofs`:
  - **Description**: Checks for Data-Oblivious Full Sequentiality (DOFS).
  - **Expected Outcome**: Not DOFS (Parallelizable). The SMT query returns UNSAT. Because the parallel branch is always taken for at least the first iteration (`k=0`), no data configuration can make the loop *fully* sequential.

- `test_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT for the same reason as the standard DOFS test.

- `test_find_dependency`:
  - **Description**: Uses a relaxed check to find if *any* dependency can exist.
  - **Expected Outcome**: Dependency exists. The SMT query returns SAT because the solver can find a value for `N` and iteration numbers `j, k` where the sequential branch is taken, creating a dependency.

#### `test_nested_loop.py`

- **Description**: Analyzes nested loops with dependencies carried by either the inner or outer loop.

- **Outer-Carried Dependency**
  - **Loop Logic**:
    ```
    for i = 1...N:
      for j = 1...M:
        A[i, j] = A[i-1, j] + B[i, j]
  ```

- **Description**: The outer loop (over `i`) has a true data dependency (`A[i,j]` depends on `A[i-1,j]`), making it sequential. The inner loop (over `j`) has no self-dependency and is parallelizable.

- `test_outer_dofs`:
  - **Description**: Checks for DOFS on both loops.
  - **Expected Outcome**: The outer loop is DOFS (Sequential, SAT). The inner loop is Not DOFS (Parallel, UNSAT).

- `test_outer_dofi`:
  - **Description**: Checks for DOFI on both loops.
  - **Expected Outcome**: The outer loop is Not DOFI (Sequential, UNSAT). The inner loop is DOFI (Parallel, SAT).

- `test_outer_find_dependency` / `test_outer_inner_find_dependency`:
  - **Description**: Uses a relaxed check for any dependency.
  - **Expected Outcome**: A dependency is found for the outer loop (SAT). No dependency is found for the inner loop (UNSAT).

- **Inner-Carried Dependency**
  - **Loop Logic**:
    ```
    for i = 1...N:
      for j = 1...M:
        A[i, j] = A[i, j-1] + B[i, j]
  ```

- **Description**: The inner loop (over `j`) has a true data dependency (`A[i,j]` depends on `A[i,j-1]`), making it sequential. The outer loop (over `i`) has no self-dependency and is parallelizable.

- `test_inner_dofs`:
  - **Description**: Checks for DOFS on both loops.
  - **Expected Outcome**: The inner loop is DOFS (Sequential, SAT). The outer loop is Not DOFS (Parallel, UNSAT).

- `test_inner_dofi`:
  - **Description**: Checks for DOFI on both loops.
  - **Expected Outcome**: The inner loop is Not DOFI (Sequential, UNSAT). The outer loop is DOFI (Parallel, SAT).

- `test_inner_find_dependency` / `test_inner_inner_find_dependency`:
  - **Description**: Uses a relaxed check for any dependency.
  - **Expected Outcome**: A dependency is found for the inner loop (SAT). No dependency is found for the outer loop (UNSAT).

#### `test_cholesky.py`

- **Description**: Models dependency patterns found in Cholesky Decomposition, which is known to be sequential.

- **Simplified Kernel**
  - **Loop Logic**:
    ```
    for i = 2...N:
      for j = 2...i:
        L[i, j] = L[i, j-1] + L[j-1, j-1]
  ```

- **Description**: This kernel simplifies the dependency structure. It contains a true Read-After-Write (RAW) dependency on `L[i, j-1]` within the inner loop, and a loop-carried dependency across the outer loop where `L[i,j]` depends on `L[j-1, j-1]`.

- `test_sequential_dofs`:
  - **Description**: Checks for DOFS on both the inner and outer loops.
  - **Expected Outcome**: Both loops are DOFS (Sequential). The SMT queries return SAT, proving dependencies exist that force sequential execution.

- `test_sequential_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: Both loops are DOFS (Sequential). SMT queries return SAT.

- `test_sequential_find_dependency`:
  - **Description**: Uses a relaxed check to find any dependency in both loops.
  - **Expected Outcome**: Dependency exists. SMT queries return SAT.

- **Full Kernel**
  - **Loop Logic**:
    ```
    for i = 0 to N-1:
      for j = 0 to i:
        sum_val = 0
        for k = 0 to j-1:
          sum_val = sum_val + L[i,k] * L[j,k]
        L[i,j] = A[i,j] - sum_val
  ```

- **Description**: This models a more complete, three-level nested loop structure for the Cholesky kernel. It is known to be fully sequential.

- `test_full_kernel_dofs`:
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.

- `test_full_kernel_dofs_forall_bounds`:
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.

- `test_full_kernel_find_dependency`:
  - **Expected Outcome**: Dependency exists. SMT query returns SAT.

#### `test_gauss_seidel.py`

- **Description**: Tests different variants of the Gauss-Seidel algorithm.

- **Traditional 1D Gauss-Seidel**
  - **Loop Logic**:
    ```
    for i = 1 to N-1:
      A[i] = A[i-1] + A[i+1]
  ```

- **Description**: This loop is inherently sequential due to a Read-After-Write (RAW) dependency where `A[i]` depends on `A[i-1]` from the current iteration.

- `test_traditional_dofs`:
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.

- `test_traditional_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: DOFS (Sequential). SMT query returns SAT.

- `test_traditional_find_dependency`:
     - **Description**: Uses a relaxed check for any dependency.
     - **Expected Outcome**: Dependency exists. SMT query returns SAT.

- **Red Pass (Parallel)**
  - **Loop Logic**:
    ```
    // Red Pass (odd indices)
    for i = 1, 3, 5, ...:
      A[i] = A[i-1] + A[i+1]
  ```

- **Description**: The Red pass involves writes to odd indices and reads from adjacent even indices. No dependency exists between iterations.

- `test_red_dofs`:
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.

- `test_red_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.

- `test_red_find_dependency`:
     - **Description**: Uses a relaxed check for any dependency.
     - **Expected Outcome**: No dependency. SMT query returns UNSAT.

- **Black Pass (Parallel)**
  - **Loop Logic**:
    ```
    // Black Pass (even indices)
    for i = 2, 4, 6, ...:
      A[i] = A[i-1] + A[i+1]
  ```

- **Description**: The Black pass involves writes to even indices and reads from adjacent odd indices. No dependency exists between iterations.

- `test_black_dofs`:
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.

- `test_black_dofs_forall_bounds`:
  - **Description**: Analyzes the same logic but with universally quantified loop bounds.
  - **Expected Outcome**: Not DOFS (Parallelizable). SMT query returns UNSAT.

- `test_black_find_dependency`:
     - **Description**: Uses a relaxed check for any dependency.
     - **Expected Outcome**: No dependency. SMT query returns UNSAT.
