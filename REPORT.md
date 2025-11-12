# P3G Test Cases Report

This report summarizes the test cases for the P3G loop analysis tool.
- The **Pseudocode** and **Expected Outcome** for each test are sourced from `README.md`.
- The **Readable Constraints** are sourced from the `.smt2` files in the `tmp/smt_simplified/readable/` directory.

---



## Basic Loops

### `test_parallel_loop.py`

#### Pseudocode
```
for i in 0:n:
  A[i] = B[i] + C[i]
```

#### Expected Outcome
Not DOFS (Parallelizable). SMT query returns UNSAT.

#### Readable Constraints
##### `parallel_loop_check.smt2`
```
DATA!C == 10003
DATA!A == 10001
DATA!B == 10002
1 <= N
ForAll(k, Not(And(1 <= N, 0 <= k, k <= -1 + N)))
```

---

### `test_sequential_loop.py`

#### Pseudocode
```
for i = 2...N:
  A[i] = A[i-1] + B[i]
```

#### Expected Outcome
DOFS (Sequential). SMT query returns SAT.

#### Readable Constraints
##### `sequential_loop_check.smt2`
```
DATA!A == 10001
DATA!B == 10002
3 <= N
True

--- Model (Witness) ---
N = 3
DATA!B = 10002
DATA!A = 10001
```

---

## Complex Access Patterns

### `test_array_reversal.py`

#### Pseudocode
```
for i = 0...N-1:
  swap(A[i], A[N-1-i])
```

#### Expected Outcome
DOFS (Sequential) for general `N` (SMT SAT); Not DOFS (Parallel) for `N >= 3` (SMT UNSAT).

#### Readable Constraints
##### `array_reversal_dofs_check.smt2`
```
DATA!A == 10001
2 <= N
ForAll(k,
       Or(2*k == -2 + N,
          N + -2*k == 2,
          Not(And(2 <= N, 0 <= k, k <= -2 + N))))

--- Model (Witness) ---
N = 2
DATA!A = 10001
```
##### `array_reversal_not_dofs_check.smt2`
```
DATA!A == 10001
3 <= N
2 <= N
ForAll(k,
       Or(Not(And(2 <= N, 0 <= k, k <= -2 + N)),
          2*k == -2 + N,
          N + -2*k == 2))
```

---

### `test_long_distance_dependency.py`

#### Pseudocode
```
for i = 2...N:
  A[i] = A[max(i-10, 0)] + B[i]
```

#### Expected Outcome
Not DOFS (Parallelizable). SMT query returns UNSAT.

#### Readable Constraints
##### `long_distance_dependency_check.smt2`
```
DATA!A == 10001
DATA!B == 10002
3 <= N
ForAll(k,
       Or(And(Not(k <= 10), k <= 9, k == 0),
          Not(And(3 <= N, 2 <= k, k <= -1 + N)),
          And(k <= 10, k <= 9, Or(-1 == k, k == 0)),
          And(k <= 10, Not(k <= 9), -1 == k)))
```

---

### `test_indirect_read_gather.py`

#### Pseudocode
```
for i = 1...N:
  A[i] = B[ IDX[i] ]
```

#### Expected Outcome
Not DOFS (Parallelizable). SMT query returns UNSAT.

#### Readable Constraints
##### `indirect_read_gather_check.smt2`
```
DATA!A == 10001
DATA!B == 10002
DATA!IDX == 10003
2 <= N
ForAll(k, Not(And(2 <= N, 1 <= k, k <= -1 + N)))
```

---

### `test_indirect_write_scatter.py`

#### Pseudocode
```
for i = 1...N:
  A[ IDX[i] ] = B[i]
```

#### Expected Outcome
Not DOFS (Parallelizable) for *some* data configurations (SMT UNSAT).

#### Readable Constraints
##### `indirect_write_scatter_check.smt2`
```
DATA!A == 10001
DATA!IDX == 10003
DATA!B == 10002
2 <= N
ForAll(k, Not(And(2 <= N, 1 <= k, k <= -1 + N)))
```

---

## Data-Dependent Analysis

### `test_data_aware_bi.py`

#### Pseudocode
```
for i = 1...N:
  if (B[i] > 0):
    A[i] = A[i-1]
```

#### Expected Outcome
DOFS (Sequential). SMT query returns SAT.

#### Readable Constraints
##### `data_aware_bi_check.smt2`
```
DATA!B == 10002
DATA!A == 10001
2 <= N
ForAll(k,
       Or(Not(And(2 <= N, 1 <= k, k <= -1 + N)),
          And(Not(B_val[k] <= 0), Not(B_val[1 + k] <= 0))))

--- Model (Witness) ---
B_val = K(Int, 2)
N = 2
DATA!B = 10002
DATA!A = 10001
```

---

### `test_data_aware_bi_b13.py`

#### Pseudocode
```
for i = 1...N:
  if (B[i] - B[13] > 0):
    A[i] = A[i-1]
```

#### Expected Outcome
DOFS (Sequential) for general `N` (SMT SAT); Not DOFS (Parallel) for `N >= 15` (SMT UNSAT).

#### Readable Constraints
##### `data_aware_bi_b13_check.smt2`
```
DATA!A == 10001
DATA!B == 10002
2 <= N
ForAll(k,
       Or(And(Not(B_val[1 + k] + -1*B_val[13] <= 0),
              DATA!B == DATA!A,
              12 == k),
          And(Not(B_val[k] + -1*B_val[13] <= 0),
              DATA!A == DATA!B,
              k == 13),
          And(Not(B_val[k] + -1*B_val[13] <= 0),
              Not(B_val[1 + k] + -1*B_val[13] <= 0)),
          Not(And(2 <= N, 1 <= k, k <= -1 + N))))

--- Model (Witness) ---
B_val = Lambda(k!0,
       If(And(2 <= k!0, Not(13 <= k!0)),
          7720,
          If(2 <= k!0,
             If(And(2 <= k!0, 13 <= k!0), 7719, 6),
             7720)))
N = 2
DATA!B = 10002
DATA!A = 10001
```
##### `data_aware_bi_b13_high_N_check.smt2`
```
DATA!A == 10001
DATA!B == 10002
15 <= N
2 <= N
ForAll(k,
       Or(And(Not(B_val[1 + k] + -1*B_val[13] <= 0),
              DATA!B == DATA!A,
              12 == k),
          Not(And(2 <= N, 1 <= k, k <= -1 + N)),
          And(Not(B_val[k] + -1*B_val[13] <= 0),
              DATA!A == DATA!B,
              k == 13),
          And(Not(B_val[k] + -1*B_val[13] <= 0),
              Not(B_val[1 + k] + -1*B_val[13] <= 0))))
```

---

### `test_sequential_with_symbolic_max_index.py`

#### Pseudocode
```
for i = 2...N:
  A[i] = A[max(i-w, 0)] + B[i]
```

#### Expected Outcome
DOFS (Sequential). SMT query returns SAT.

#### Readable Constraints
##### `sequential_with_symbolic_max_index_check.smt2`
```
DATA!B == 10002
DATA!A == 10001
3 <= N
ForAll(k,
       Or(w == -1,
          And(k + -1*w <= 0, Or(k == 0, w == 1, -1 == k)),
          And(Not(k + -1*w <= 0),
              Or(w == -1, k == 0, w == 1)),
          And(Not(k + -1*w <= 0),
              Not(k + -1*w <= -1),
              Or(w == -1, w == 1)),
          Not(And(3 <= N, 2 <= k, k <= -1 + N)),
          And(k + -1*w <= 0,
              k + -1*w <= -1,
              Or(k == 0, -1 == k)),
          k == 0,
          And(k + -1*w <= -1, Or(w == -1, k == 0, -1 == k)),
          And(k + -1*w <= 0,
              Not(k + -1*w <= -1),
              Or(w == 1, -1 == k)),
          w == 1,
          -1 == k,
          And(Not(k + -1*w <= 0),
              k + -1*w <= -1,
              Or(w == -1, k == 0)),
          And(Not(k + -1*w <= -1),
              Or(w == -1, w == 1, -1 == k))))

--- Model (Witness) ---
w = 1
N = 3
DATA!B = 10002
DATA!A = 10001
```

---

## Other Cases

### `test_non_linear_predicate.py`

#### Pseudocode
```
for i=0:N:
  if i*i <= N:
    A[i] = B[i] + C[i]  // Parallel part
  else:
    A[i] = A[i-1] + C[i] // Sequential part
```

#### Expected Outcome
Not DOFS (Parallelizable). SMT query returns UNSAT.

#### Readable Constraints
##### `non_linear_predicate_check.smt2`
```
DATA!A == 10001
DATA!B == 10002
DATA!C == 10003
1 <= N
ForAll(k,
       Or(And(Not(k*k <= N), Not((1 + k)*(1 + k) <= N)),
          And(k*k <= N, Not((1 + k)*(1 + k) <= N)),
          Not(And(1 <= N, 0 <= k, k <= -1 + N))))
```

---

### `test_nested_loop.py`

#### `test_nested_loop_outer_dofs`

#### Pseudocode
```
for i = 1...N:
  for j = 1...M:
    A[i, j] = A[i-1, j] + B[i, j]
```

#### Expected Outcome
Outer Loop DOFS (Sequential); Inner Loop Not DOFS (Parallel).

#### Readable Constraints
##### `nested_loop_outer_dofs_outer_check.smt2`
```
DATA!B == 10002
DATA!A == 10001
2 <= N
True

--- Model (Witness) ---
N = 2
DATA!B = 10002
DATA!A = 10001
```
##### `nested_loop_outer_dofs_inner_check.smt2`
```
DATA!B == 10002
DATA!A == 10001
2 <= M
ForAll(j, Not(And(2 <= M, 1 <= j, j <= -1 + M)))
```

---

#### `test_nested_loop_inner_dofs`

#### Pseudocode
```
for i = 1...N:
  for j = 1...M:
    A[i, j] = A[i, j-1] + B[i, j]
```

#### Expected Outcome
Outer Loop Not DOFS (Parallel); Inner Loop DOFS (Sequential).

#### Readable Constraints
##### `nested_loop_inner_dofs_check.smt2`
```
DATA!A == 10001
DATA!B == 10002
2 <= M
True

--- Model (Witness) ---
M = 2
DATA!B = 10002
DATA!A = 10001
```
##### `nested_loop_outer_not_dofs_check.smt2`
```
DATA!A == 10001
DATA!B == 10002
2 <= N
ForAll(i, Not(And(2 <= N, 1 <= i, i <= -1 + N)))
```

---

### `test_cholesky.py`

#### `test_cholesky_sequential`

#### Pseudocode
```
// Simplified Cholesky
for i = 2...N:
  for j = 2...i:
    L[i, j] = L[i, j-1] + L[j-1, j-1]
```

#### Expected Outcome
Inner Loop DOFS (Sequential); Outer Loop Not DOFS (Parallel).

#### Readable Constraints
##### `cholesky_inner.smt2`
```
DATA!L == 10001
3 <= i
True

--- Model (Witness) ---
i = 3
DATA!L = 10001
```
##### `cholesky_outer.smt2`
```
DATA!L == 10001
3 <= N
ForAll(i, Not(And(3 <= N, 2 <= i, i <= -1 + N)))
```

---

#### `test_cholesky_full_kernel`

#### Pseudocode
```
// Full Cholesky Kernel (simplified for P3G modeling)
for i = 0 to N-1:
  for j = 0 to i:
    sum_val = 0
    for k = 0 to j-1:
      sum_val = sum_val + L[i,k] * L[j,k]
    L[i,j] = A[i,j] - sum_val
```

#### Expected Outcome
Full Cholesky Kernel DOFS (Sequential).

#### Readable Constraints
##### `cholesky_full_kernel.smt2`
```
DATA!L == 10002
DATA!A == 10001
DATA!sum_val == 10003
2 <= N
True

--- Model (Witness) ---
N = 2
DATA!L = 10002
DATA!sum_val = 10003
DATA!A = 10001
```

---

### `test_gauss_seidel.py`

#### `test_gauss_seidel_red_black`

#### Pseudocode
```
// Red Pass (odd indices)
for i = 1, 3, 5, ...:
  A[i] = A[i-1] + A[i+1]

// Black Pass (even indices)
for i = 2, 4, 6, ...:
  A[i] = A[i-1] + A[i+1]
```

#### Expected Outcome
Both Red and Black Passes Not DOFS (Parallelizable). SMT query returns UNSAT.

#### Readable Constraints
##### `gauss_seidel_red.smt2`
```
DATA!A == 10001
ToReal(N) >= 4
ForAll(k,
       Not(And(ToReal(N) >= 4,
               0 <= k,
               ToReal(k) <= -2 + 1/2*ToReal(N))))
```
##### `gauss_seidel_black.smt2`
```
DATA!A == 10001
ToReal(N) >= 6
ForAll(k,
       Not(And(ToReal(N) >= 6,
               0 <= k,
               ToReal(k) <= -3 + 1/2*ToReal(N))))
```

---

#### `test_gauss_seidel_traditional`

#### Pseudocode
```
// Traditional 1D Gauss-Seidel
for i = 1 to N-1:
  A[i] = A[i-1] + A[i+1]
```

#### Expected Outcome
Traditional 1D Gauss-Seidel DOFS (Sequential). SMT query returns SAT.

#### Readable Constraints
##### `gauss_seidel_traditional.smt2`
```
DATA!A == 10001
3 <= N
True

--- Model (Witness) ---
N = 3
DATA!A = 10001
```

---