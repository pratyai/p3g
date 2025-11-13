# P3G Test Cases Report

This report summarizes the test cases for the P3G loop analysis tool.

- The **Pseudocode** and **Expected Outcome** for each test are sourced from `README.md` .
- The **Readable Constraints** are sourced from the `.smt2` files in the `tmp/smt_simplified/readable/` directory.

---

## Basic Loops

### `test_parallel_loop.py`

#### Pseudocode

```
for i in 0:n:
  A[i] = B[i] + C[i]
```

#### Description

This loop is inherently parallelizable as each iteration is independent, reading from `B` and `C` and writing to `A` at the current index `i` . There are no dependencies between adjacent iterations that would force sequential execution.

#### Expected Outcome

** `test_parallel_loop_dofs` **: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
** `test_parallel_loop_dofs_forall_bounds` **: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### SMT Analysis

##### `parallel_loop_dofs.smt2`

```
DATA!C == 10003
DATA!A == 10001
DATA!B == 10002
1 <= N
ForAll(k, Not(And(1 <= N, 0 <= k, k <= -1 + N)))
```

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `UNSAT` result confirms that no such data configuration (and loop bound) exists that makes the loop fully sequential, thus proving the loop is Not DOFS (parallelizable).

##### `parallel_loop_dofs_forall_bounds.smt2`

```
DATA!A == 10001
DATA!C == 10003
DATA!B == 10002
1 <= N
ForAll([k, N], Not(And(1 <= N, 0 <= k, k <= -1 + N)))
```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `UNSAT` result indicates that for *every* possible loop bound, there is no data configuration that forces sequentiality. This strongly implies the loop is Not DOFS (parallelizable) across all valid loop bounds.

---

### `test_sequential_loop.py`

#### Pseudocode

```
for i = 2...N:
  A[i] = A[i-1] + B[i]
```

#### Description

This loop has a Read-After-Write (RAW) dependency where `A[i]` reads `A[i-1]` , which was written in the previous iteration. This dependency exists for all iterations, making the loop inherently sequential.

#### Expected Outcome

** `test_sequential_loop_dofs` **: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
** `test_sequential_loop_dofs_forall_bounds` **: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

#### SMT Analysis

##### `sequential_loop_dofs.smt2`

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

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `SAT` result indicates that such a data configuration (and loop bound) exists (e.g., `N=3` ), making the loop fully sequential (DOFS).

##### `sequential_loop_dofs_forall_bounds.smt2`

```
DATA!B == 10002
DATA!A == 10001
3 <= N
True

--- Model (Witness) ---
N = 3
DATA!B = 10002
DATA!A = 10001
```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `SAT` result indicates that for *every* possible loop bound, there exists a data configuration that forces sequentiality. This means the loop is DOFS (sequential) for all loop bounds.

---

## Complex Access Patterns

### `test_array_reversal.py`

#### Pseudocode

```
for i = 0...N-1:
  swap(A[i], A[N-1-i])
```

#### Description

This loop swaps elements `A[i]` and `A[N-1-i]` . The parallelizability depends on the value of `N` .

#### Expected Outcome

** `test_array_reversal_dofs` **: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality (e.g., for `N=2` ).
** `test_array_reversal_high_N_dofs` **: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality when `N >= 3` .
** `test_array_reversal_dofs_forall_bounds` **: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

#### SMT Analysis

##### `array_reversal_dofs.smt2`

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

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `SAT` result indicates that such a data configuration (and loop bound) exists. The `Model (Witness)` shows that for `N=2` , a dependency is found (e.g., `A[0]` and `A[1]` are swapped), making the loop fully sequential (DOFS).

##### `array_reversal_high_N_dofs.smt2`

```
DATA!A == 10001
3 <= N
2 <= N
ForAll(k,
       Or(Not(And(2 <= N, 0 <= k, k <= -2 + N)),
          2*k == -2 + N,
          N + -2*k == 2))
```

*Interpretation*: This SMT query, with the additional constraint `N >= 3` , attempts to find a data configuration (including loop bounds as data) that forces a dependency. The `UNSAT` result indicates that no such data configuration (and loop bound) exists when `N >= 3` , meaning the loop is parallelizable under this condition.

##### `array_reversal_dofs_forall_bounds.smt2`

```
DATA!A == 10001
2 <= N
ForAll([k, N],
       Or(2*k == -2 + N,
          Not(And(2 <= N, 0 <= k, k <= -2 + N)),
          N + -2*k == 2))
```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `SAT` result indicates that for *every* possible loop bound, there exists a data configuration that forces sequentiality. This means the loop is DOFS (sequential) for all loop bounds.

---

### `test_long_distance_dependency.py`

#### Pseudocode

```
for i = 2...N:
  A[i] = A[max(i-10, 0)] + B[i]
```

#### Description

`A[i]` depends on `A[max(i-10, 0)]` , a value far removed from `A[i-1]` . This means there is no inherent data dependency between *adjacent* iterations that would force sequential execution.

#### Expected Outcome

** `test_long_distance_dependency_dofs` **: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
** `test_long_distance_dependency_dofs_forall_bounds` **: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### SMT Analysis

##### `long_distance_dependency_dofs.smt2`

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

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `UNSAT` result confirms that no such data configuration (and loop bound) exists that makes the loop fully sequential, thus proving the loop is Not DOFS (parallelizable).

##### `long_distance_dependency_dofs_forall_bounds.smt2`

```
DATA!A == 10001
DATA!B == 10002
3 <= N
ForAll([k, N],
       Or(Not(And(3 <= N, 2 <= k, k <= -1 + N)),
          And(Not(k <= 10), k <= 9, k == 0),
          And(k <= 10, Not(k <= 9), -1 == k),
          And(k <= 10, k <= 9, Or(-1 == k, k == 0))))
```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `UNSAT` result indicates that for *every* possible loop bound, there is no data configuration that forces sequentiality. This strongly implies the loop is Not DOFS (parallelizable) across all valid loop bounds.

---

### `test_indirect_read_gather.py`

#### Pseudocode

```
for i = 1...N:
  A[i] = B[ IDX[i] ]
```

#### Description

This operation is generally parallelizable because writes to `A[i]` are independent of previous `A` values, and reads from `B` are indirect. There is no inherent data dependency between adjacent iterations that would force sequential execution for all data configurations.

#### Expected Outcome

** `test_indirect_read_gather_dofs` **: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
** `test_indirect_read_gather_dofs_forall_bounds` **: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### SMT Analysis

##### `indirect_read_gather_dofs.smt2`

```
DATA!A == 10001
DATA!B == 10002
DATA!IDX == 10003
2 <= N
ForAll(k, Not(And(2 <= N, 1 <= k, k <= -1 + N)))
```

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `UNSAT` result confirms that no such data configuration (and loop bound) exists that makes the loop fully sequential, thus proving the loop is Not DOFS (parallelizable).

##### `indirect_read_gather_dofs_forall_bounds.smt2`

```
DATA!B == 10002
DATA!A == 10001
DATA!IDX == 10003
2 <= N
ForAll([k, N], Not(And(2 <= N, 1 <= k, k <= -1 + N)))
```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `UNSAT` result indicates that for *every* possible loop bound, there is no data configuration that forces sequentiality. This strongly implies the loop is Not DOFS (parallelizable) across all valid loop bounds.

---

### `test_indirect_write_scatter.py`

#### Pseudocode

```
for i = 1...N:
  A[ IDX[i] ] = B[i]
```

#### Description

This operation is generally sequential because multiple iterations can write to the same memory location in `A` if `IDX[i]` values are not unique or create dependencies (e.g., WAW if `IDX[i]=5` for all `i` ). The test proves *existence* of a sequentializing data configuration.

#### Expected Outcome

** `test_indirect_write_scatter_dofs` **: Not DOFS (Parallelizable) for *some* data configurations. SMT query returns UNSAT, proving that no data configuration forces sequentiality across *all* adjacent iterations.
** `test_indirect_write_scatter_dofs_forall_bounds` **: Not DOFS (Parallelizable) for *some* data configurations. SMT query returns UNSAT, proving that no data configuration forces sequentiality across *all* adjacent iterations.

#### SMT Analysis

##### `indirect_write_scatter_dofs.smt2`

```
DATA!A == 10001
DATA!IDX == 10003
DATA!B == 10002
2 <= N
ForAll(k, Not(And(2 <= N, 1 <= k, k <= -1 + N)))
```

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `UNSAT` result confirms that no such data configuration (and loop bound) exists that makes the loop fully sequential, thus proving the loop is Not DOFS (parallelizable).

##### `indirect_write_scatter_dofs_forall_bounds.smt2`

```
DATA!B == 10002
DATA!IDX == 10003
DATA!A == 10001
2 <= N
ForAll([k, N], Not(And(2 <= N, 1 <= k, k <= -1 + N)))
```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `UNSAT` result indicates that for *every* possible loop bound, there is no data configuration that forces sequentiality. This strongly implies the loop is Not DOFS (parallelizable) across all valid loop bounds.

---

## Data-Dependent Analysis

### `test_data_aware_bi.py`

#### Pseudocode

```
for i = 1...N:
  if (B[i] > 0):
    A[i] = A[i-1]
```

#### Description

This loop's dependency is conditional on the data in `B` . If all `B[i] > 0` , then `A[i] = A[i-1]` always executes, creating a sequential dependency.

#### Expected Outcome

** `test_data_aware_bi_dofs` **: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
** `test_data_aware_bi_dofs_forall_bounds` **: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

#### SMT Analysis

##### `data_aware_bi_dofs.smt2`

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

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `SAT` result indicates that such a data configuration (and loop bound, e.g., `N=2` ) exists, making the loop fully sequential (DOFS).

##### `data_aware_bi_dofs_forall_bounds.smt2`

```
DATA!B == 10002
DATA!A == 10001
2 <= N
ForAll([k, N],
       Or(Not(And(2 <= N, 1 <= k, k <= -1 + N)),
          And(Not(B_val[k] <= 0), Not(B_val[1 + k] <= 0))))

--- Model (Witness) ---
B_val = Lambda(k!0,
       If(And(2 <= k!0,
              3 <= k!0,
              4 <= k!0,
              5 <= k!0,
              6 <= k!0,
              7 <= k!0,
              8 <= k!0,
              9 <= k!0,
              10 <= k!0,
              Not(11 <= k!0)),
          610,
          <redacted>
       ))

N = 2
DATA!B = 10002
DATA!A = 10001
```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `SAT` result indicates that for *every* possible loop bound, there exists a data configuration that forces sequentiality. This means the loop is DOFS (sequential) for all loop bounds.

---

### `test_data_aware_bi_b13.py`

#### Pseudocode

```
for i = 1...N:
  if (B[i] - B[13] > 0):
    A[i] = A[i-1]
```

#### Description

This loop's dependency is conditional on the difference between `B[i]` and a constant `B[13]` .

#### Expected Outcome

** `test_data_aware_bi_b13_dofs` **: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality (e.g., if `B[i]=1` and `B[13]=0` , the condition is always true).
** `test_data_aware_bi_b13_high_N_dofs` **: Not DOFS (Parallel). SMT query returns UNSAT, proving that no data configuration forces sequentiality when `N >= 15` (because for `k=13` , the condition `B[13] - B[13] > 0` is false).
** `test_data_aware_bi_b13_dofs_forall_bounds` **: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

#### SMT Analysis

##### `data_aware_bi_b13_dofs.smt2`

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

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `SAT` result indicates that such a data configuration (and loop bound, e.g., `N=2` ) exists, making the loop fully sequential (DOFS).

##### `data_aware_bi_b13_high_N_dofs.smt2`

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

*Interpretation*: This SMT query, with the additional constraint `N >= 15` , attempts to find a data configuration (including loop bounds as data) that forces a dependency. The `UNSAT` result indicates that no such data configuration (and loop bound) exists when `N >= 15` , meaning the loop is parallelizable under this condition.

##### `data_aware_bi_b13_dofs_forall_bounds.smt2`

```
DATA!B == 10002
DATA!A == 10001
2 <= N
ForAll([k, N],
       Or(Not(And(2 <= N, 1 <= k, k <= -1 + N)),
          And(Not(B_val[k] + -1*B_val[13] <= 0),
              Not(B_val[1 + k] + -1*B_val[13] <= 0)),
          And(Not(B_val[k] + -1*B_val[13] <= 0),
              DATA!A == DATA!B,
              k == 13),
          And(Not(B_val[1 + k] + -1*B_val[13] <= 0),
              DATA!B == DATA!A,
              12 == k)))
```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `SAT` result indicates that for *every* possible loop bound, there exists a data configuration that forces sequentiality. This means the loop is DOFS (sequential) for all loop bounds.

---

### `test_sequential_with_symbolic_max_index.py`

#### Pseudocode

```

for i = 2...N:
  A[i] = A[max(i-w, 0)] + B[i]

```

#### Description

This loop's dependency involves a symbolic variable `w` in the `max` function. Since `w` is symbolic, the SMT solver can choose `w=1` , making the loop `A[i] = A[i-1] + B[i]` (sequential). Thus, a data configuration exists that forces sequentiality.

#### Expected Outcome

** `test_sequential_with_symbolic_max_index_dofs` **: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.
** `test_sequential_with_symbolic_max_index_dofs_forall_bounds` **: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

#### SMT Analysis

##### `sequential_with_symbolic_max_index_dofs.smt2`

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

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds and symbolic variable `w` as data) that forces a dependency between adjacent iterations. The `SAT` result indicates that such a data configuration (and loop bound) exists. The `Model (Witness)` shows that for `N=3` and `w=1` , the loop becomes sequential.

##### `sequential_with_symbolic_max_index_dofs_forall_bounds.smt2`

```

DATA!B == 10002
DATA!A == 10001
3 <= N
ForAll([k, N],
       Or(And(Not(k + -1*w <= -1),
              Or(w == -1, -1 == k, w == 1)),
          k == 0,
          w == -1,
          Not(And(3 <= N, 2 <= k, k <= -1 + N)),
          And(k + -1*w <= 0, Or(k == 0, -1 == k, w == 1)),
          And(k + -1*w <= 0,
              k + -1*w <= -1,
              Or(k == 0, -1 == k)),
          And(k + -1*w <= -1, Or(k == 0, w == -1, -1 == k)),
          And(k + -1*w <= 0,
              Not(k + -1*w <= -1),
              Or(-1 == k, w == 1)),
          -1 == k,
          And(Not(k + -1*w <= 0),
              Or(k == 0, w == -1, w == 1)),
          And(Not(k + -1*w <= 0),
              k + -1*w <= -1,
              Or(k == 0, w == -1)),
          And(Not(k + -1*w <= 0),
              Not(k + -1*w <= -1),
              Or(w == -1, w == 1)),
          w == 1))

--- Model (Witness) ---
N = 3
w = 1
DATA!B = 10002
DATA!A = 10001

```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration (including symbolic variable `w` ) that forces a dependency. The `SAT` result indicates that for *every* possible loop bound, there exists a data configuration (e.g., `w=1` ) that forces sequentiality. This means the loop is DOFS (sequential) for all loop bounds.

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

#### Description

This loop contains a non-linear predicate ( `i*i <= N` ) that determines whether a parallel or sequential branch is taken. Because the parallel branch ( `A[i] = B[i] + C[i]` ) can always be taken for some `k` (e.g., for `k=0` , `0*0 <= N` is always true for `N >= 0` ), there is no data configuration that forces *all* adjacent iterations to be sequential.

#### Expected Outcome

** `test_non_linear_predicate_dofs` **: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.
** `test_non_linear_predicate_dofs_forall_bounds` **: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### SMT Analysis

##### `non_linear_predicate_dofs.smt2`

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

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `UNSAT` result confirms that no such data configuration (and loop bound) exists that makes the loop fully sequential, thus proving the loop is Not DOFS (parallelizable).

##### `non_linear_predicate_dofs_forall_bounds.smt2`

```

DATA!C == 10003
DATA!B == 10002
DATA!A == 10001
1 <= N
ForAll([k, N],
       Or(Not(And(1 <= N, 0 <= k, k <= -1 + N)),
          And(k*k <= N, Not((1 + k)*(1 + k) <= N)),
          And(Not(k*k <= N), Not((1 + k)*(1 + k) <= N))))

```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `UNSAT` result indicates that for *every* possible loop bound, there is no data configuration that forces sequentiality. This strongly implies the loop is Not DOFS (parallelizable) across all valid loop bounds.

---

### `test_nested_loop.py`

#### `test_nested_loop_outer_dofs`

#### Pseudocode

```

for i = 1...N:
  for j = 1...M:
    A[i, j] = A[i-1, j] + B[i, j]

```

#### Description

The outer loop (over `i` ) has a true data dependency ( `A[i,j]` depends on `A[i-1,j]` ), making it DOFS. The inner loop (over `j` ) has no self-dependency, making it Not DOFS (parallelizable).

#### Expected Outcome

**Outer Loop ( `nested_loop_outer_dofs_outer_dofs` )**: DOFS (Sequential). SMT query returns SAT.
**Inner Loop ( `nested_loop_outer_dofs_inner_dofs` )**: Not DOFS (Parallel). SMT query returns UNSAT.

#### SMT Analysis

##### `nested_loop_outer_dofs_outer_dofs.smt2`

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

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations of the *outer* loop. The `SAT` result indicates that such a data configuration (and loop bound, e.g., `N=2` ) exists, making the outer loop fully sequential (DOFS).

##### `nested_loop_outer_dofs_inner_dofs.smt2`

```

DATA!B == 10002
DATA!A == 10001
2 <= M
ForAll(j, Not(And(2 <= M, 1 <= j, j <= -1 + M)))

```

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations of the *inner* loop. The `UNSAT` result confirms that no such data configuration (and loop bound) exists that makes the inner loop fully sequential, thus proving the inner loop is Not DOFS (parallelizable).

#### `test_nested_loop_outer_dofs_forall_bounds`

#### Pseudocode

```

for i = 1...N:
  for j = 1...M:
    A[i, j] = A[i-1, j] + B[i, j]

```

#### Description

Analyzes the same loop logic as `test_nested_loop_outer_dofs` , but using loop bounds SMT generation. The outer loop (over `i` ) has a true data dependency ( `A[i,j]` depends on `A[i-1,j]` ), making it DOFS. The inner loop (over `j` ) has no self-dependency, making it Not DOFS (parallelizable).

#### Expected Outcome

**Outer Loop ( `nested_loop_outer_dofs_outer_dofs_forall_bounds` )**: DOFS (Sequential). SMT query returns SAT.
**Inner Loop ( `nested_loop_outer_dofs_inner_dofs_forall_bounds` )**: Not DOFS (Parallel). SMT query returns UNSAT.

#### SMT Analysis

##### `nested_loop_outer_dofs_outer_dofs_forall_bounds.smt2`

```

DATA!A == 10001
DATA!B == 10002
2 <= N
True

--- Model (Witness) ---
N = 2
DATA!B = 10002
DATA!A = 10001

```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency between adjacent iterations of the *outer* loop. The `SAT` result indicates that for *every* possible loop bound, there exists a data configuration that forces sequentiality. This means the outer loop is DOFS (sequential) for all loop bounds.

##### `nested_loop_outer_dofs_inner_dofs_forall_bounds.smt2`

```

DATA!A == 10001
DATA!B == 10002
2 <= M
ForAll([j, M], Not(And(2 <= M, 1 <= j, j <= -1 + M)))

```

*Interpretation*: This query universally quantifies `M` (loop bounds) and attempts to find a data configuration that forces a dependency between adjacent iterations of the *inner* loop. The `UNSAT` result indicates that for *every* possible loop bound, there is no data configuration that forces sequentiality. This strongly implies the inner loop is Not DOFS (parallelizable) across all valid loop bounds.

---

#### `test_nested_loop_inner_dofs`

#### Pseudocode

```

for i = 1...N:
  for j = 1...M:
    A[i, j] = A[i, j-1] + B[i, j]

```

#### Description

The outer loop (over `i` ) has no self-dependency, making it Not DOFS (parallelizable). The inner loop (over `j` ) has a true data dependency ( `A[i,j]` depends on `A[i,j-1]` ), making it DOFS.

#### Expected Outcome

**Outer Loop ( `nested_loop_inner_dofs_outer_dofs` )**: Not DOFS (Parallel). SMT query returns UNSAT.
**Inner Loop ( `nested_loop_inner_dofs_inner_dofs` )**: DOFS (Sequential). SMT query returns SAT.

#### SMT Analysis

##### `nested_loop_inner_dofs_inner_dofs.smt2`

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

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations of the *inner* loop. The `SAT` result indicates that such a data configuration (and loop bound, e.g., `M=2` ) exists, making the inner loop fully sequential (DOFS).

##### `nested_loop_inner_dofs_outer_dofs.smt2`

```

DATA!A == 10001
DATA!B == 10002
2 <= N
ForAll(i, Not(And(2 <= N, 1 <= i, i <= -1 + N)))

```

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations of the *outer* loop. The `UNSAT` result confirms that no such data configuration (and loop bound) exists that makes the outer loop fully sequential, thus proving the outer loop is Not DOFS (parallelizable).

#### `test_nested_loop_inner_dofs_forall_bounds`

#### Pseudocode

```

for i = 1...N:
  for j = 1...M:
    A[i, j] = A[i, j-1] + B[i, j]

```

#### Description

Analyzes the same loop logic as `test_nested_loop_inner_dofs` , but using loop bounds SMT generation. The outer loop (over `i` ) has no self-dependency, making it Not DOFS (parallelizable). The inner loop (over `j` ) has a true data dependency ( `A[i,j]` depends on `A[i,j-1]` ), making it DOFS.

#### Expected Outcome

**Outer Loop ( `nested_loop_inner_dofs_outer_dofs_forall_bounds` )**: Not DOFS (Parallel). SMT query returns UNSAT.
**Inner Loop ( `nested_loop_inner_dofs_inner_dofs_forall_bounds` )**: DOFS (Sequential). SMT query returns SAT.

#### SMT Analysis

##### `nested_loop_inner_dofs_inner_dofs_forall_bounds.smt2`

```

DATA!B == 10002
DATA!A == 10001
2 <= M
True

--- Model (Witness) ---
M = 2
DATA!B = 10002
DATA!A = 10001

```

*Interpretation*: This query universally quantifies `M` (loop bounds) and attempts to find a data configuration that forces a dependency between adjacent iterations of the *inner* loop. The `SAT` result indicates that for *every* possible loop bound, there exists a data configuration that forces sequentiality. This means the inner loop is DOFS (sequential) for all loop bounds.

##### `nested_loop_inner_dofs_outer_dofs_forall_bounds.smt2`

```

DATA!B == 10002
DATA!A == 10001
2 <= N
ForAll([i, N], Not(And(2 <= N, 1 <= i, i <= -1 + N)))

```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency between adjacent iterations of the *outer* loop. The `UNSAT` result indicates that for *every* possible loop bound, there is no data configuration that forces sequentiality. This strongly implies the outer loop is Not DOFS (parallelizable) across all valid loop bounds.

---

### `test_cholesky.py`

#### `test_cholesky_sequential_dofs`

#### Pseudocode

```

// Simplified Cholesky
for i = 2...N:
  for j = 2...i:
    L[i, j] = L[i, j-1] + L[j-1, j-1]

```

#### Description

This test models a simplified dependency pattern. It analyzes both the inner and outer loops of this simplified kernel. The inner loop has a true data dependency, making it DOFS. The outer loop has no self-dependency, making it Not DOFS (parallelizable).

#### Expected Outcome

**Inner Loop ( `cholesky_sequential_inner_dofs` )**: DOFS (Sequential). SMT query returns SAT.
**Outer Loop ( `cholesky_sequential_outer_dofs` )**: Not DOFS (Parallel). SMT query returns UNSAT.

#### SMT Analysis

##### `cholesky_sequential_inner_dofs.smt2`

```

DATA!L == 10001
3 <= i
True

--- Model (Witness) ---
i = 3
DATA!L = 10001

```

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations of the *inner* loop. The `SAT` result indicates that such a data configuration (and loop bound, e.g., `i=3` ) exists, making the inner loop fully sequential (DOFS).

##### `cholesky_sequential_outer_dofs.smt2`

```

DATA!L == 10001
3 <= N
ForAll(i, Not(And(3 <= N, 2 <= i, i <= -1 + N)))

```

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations of the *outer* loop. The `UNSAT` result confirms that no such data configuration (and loop bound) exists that makes the outer loop fully sequential, thus proving the outer loop is Not DOFS (parallelizable).

#### `test_cholesky_sequential_dofs_forall_bounds`

#### Pseudocode

```

// Simplified Cholesky
for i = 2...N:
  for j = 2...i:
    L[i, j] = L[i, j-1] + L[j-1, j-1]

```

#### Description

Analyzes the same loop logic as `test_cholesky_sequential_dofs` , but using loop bounds SMT generation. The inner loop has a true data dependency, making it DOFS. The outer loop has no self-dependency, making it Not DOFS (parallelizable).

#### Expected Outcome

**Inner Loop ( `cholesky_sequential_inner_dofs_forall_bounds` )**: DOFS (Sequential). SMT query returns SAT.
**Outer Loop ( `cholesky_sequential_outer_dofs_forall_bounds` )**: Not DOFS (Parallel). SMT query returns UNSAT.

#### SMT Analysis

##### `cholesky_sequential_inner_dofs_forall_bounds.smt2`

```

DATA!L == 10001
3 <= i
True

--- Model (Witness) ---
i = 3
DATA!L = 10001

```

*Interpretation*: This query universally quantifies `i` (loop bounds) and attempts to find a data configuration that forces a dependency between adjacent iterations of the *inner* loop. The `SAT` result indicates that for *every* possible loop bound, there exists a data configuration that forces sequentiality. This means the inner loop is DOFS (sequential) for all loop bounds.

##### `cholesky_sequential_outer_dofs_forall_bounds.smt2`

```

DATA!L == 10001
3 <= N
ForAll([i, N], Not(And(3 <= N, 2 <= i, i <= -1 + N)))

```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency between adjacent iterations of the *outer* loop. The `UNSAT` result indicates that for *every* possible loop bound, there is no data configuration that forces sequentiality. This strongly implies the outer loop is Not DOFS (parallelizable) across all valid loop bounds.

---

#### `test_cholesky_full_kernel_dofs`

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

#### Description

This test models a more accurate Cholesky Decomposition kernel. It is highly sequential due to dependencies across all three nested loops.

#### Expected Outcome

**Full Cholesky Kernel ( `cholesky_full_kernel_dofs` )**: DOFS (Sequential). SMT query returns SAT.

#### SMT Analysis

##### `cholesky_full_kernel_dofs.smt2`

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

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `SAT` result indicates that such a data configuration (and loop bound, e.g., `N=2` ) exists, making the full Cholesky kernel fully sequential (DOFS).

#### `test_cholesky_full_kernel_dofs_forall_bounds`

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

#### Description

Analyzes the same loop logic as `test_cholesky_full_kernel_dofs` , but using loop bounds SMT generation. This test models a more accurate Cholesky Decomposition kernel. It is highly sequential due to dependencies across all three nested loops.

#### Expected Outcome

**Full Cholesky Kernel ( `cholesky_full_kernel_dofs_forall_bounds` )**: DOFS (Sequential). SMT query returns SAT.

#### SMT Analysis

##### `cholesky_full_kernel_dofs_forall_bounds.smt2`

```

DATA!sum_val == 10003
DATA!A == 10001
DATA!L == 10002
2 <= N
True

--- Model (Witness) ---
N = 2
DATA!L = 10002
DATA!sum_val = 10003
DATA!A = 10001

```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `SAT` result indicates that for *every* possible loop bound, there exists a data configuration that forces sequentiality. This means the full Cholesky kernel is DOFS (sequential) for all loop bounds.

---

### `test_gauss_seidel.py`

#### `test_gauss_seidel_red_dofs`

#### Pseudocode

```

// Red Pass (odd indices)
for i = 1, 3, 5, ...:
  A[i] = A[i-1] + A[i+1]

```

#### Description

This test covers the Red pass of Gauss-Seidel. It involves writes to odd indices and reads from adjacent even indices. No dependency between iterations for any data configuration, making it parallel.

#### Expected Outcome

**Red Pass ( `gauss_seidel_red_dofs` )**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### SMT Analysis

##### `gauss_seidel_red_dofs.smt2`

```

DATA!A == 10001
ToReal(N) >= 4
ForAll(k,
       Not(And(ToReal(N) >= 4,
               0 <= k,
               ToReal(k) <= -2 + 1/2*ToReal(N))))

```

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `UNSAT` result confirms that no such data configuration (and loop bound) exists that makes the loop fully sequential, thus proving the loop is Not DOFS (parallelizable).

#### `test_gauss_seidel_red_dofs_forall_bounds`

#### Pseudocode

```

// Red Pass (odd indices)
for i = 1, 3, 5, ...:
  A[i] = A[i-1] + A[i+1]

```

#### Description

Analyzes the same loop logic as `test_gauss_seidel_red_dofs` , but using loop bounds SMT generation. This test covers the Red pass of Gauss-Seidel. It involves writes to odd indices and reads from adjacent even indices. No dependency between iterations for any data configuration, making it parallel.

#### Expected Outcome

**Red Pass ( `gauss_seidel_red_dofs_forall_bounds` )**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### SMT Analysis

##### `gauss_seidel_red_dofs_forall_bounds.smt2`

```

DATA!A == 10001
ToReal(N) >= 4
ForAll([k, N],
       Not(And(ToReal(N) >= 4,
               0 <= k,
               ToReal(k) <= -2 + 1/2*ToReal(N))))

```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `UNSAT` result indicates that for *every* possible loop bound, there is no data configuration that forces sequentiality. This strongly implies the loop is Not DOFS (parallelizable) across all valid loop bounds.

---

#### `test_gauss_seidel_black_dofs`

#### Pseudocode

```

// Black Pass (even indices)
for i = 2, 4, 6, ...:
  A[i] = A[i-1] + A[i+1]

```

#### Description

This test covers the Black pass of Gauss-Seidel. It involves writes to even indices and reads from adjacent odd indices. No dependency between iterations for any data configuration, making it parallel.

#### Expected Outcome

**Black Pass ( `gauss_seidel_black_dofs` )**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### SMT Analysis

##### `gauss_seidel_black_dofs.smt2`

```

DATA!A == 10001
ToReal(N) >= 6
ForAll(k,
       Not(And(ToReal(N) >= 6,
               0 <= k,
               ToReal(k) <= -3 + 1/2*ToReal(N))))

```

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `UNSAT` result confirms that no such data configuration (and loop bound) exists that makes the loop fully sequential, thus proving the loop is Not DOFS (parallelizable).

#### `test_gauss_seidel_black_dofs_forall_bounds`

#### Pseudocode

```

// Black Pass (even indices)
for i = 2, 4, 6, ...:
  A[i] = A[i-1] + A[i+1]

```

#### Description

Analyzes the same loop logic as `test_gauss_seidel_black_dofs` , but using loop bounds SMT generation. This test covers the Black pass of Gauss-Seidel. It involves writes to even indices and reads from adjacent odd indices. No dependency between iterations for any data configuration, making it parallel.

#### Expected Outcome

**Black Pass ( `gauss_seidel_black_dofs_forall_bounds` )**: Not DOFS (Parallelizable). SMT query returns UNSAT, proving that no data configuration forces sequentiality.

#### SMT Analysis

##### `gauss_seidel_black_dofs_forall_bounds.smt2`

```

DATA!A == 10001
ToReal(N) >= 6
ForAll([k, N],
       Not(And(ToReal(N) >= 6,
               0 <= k,
               ToReal(k) <= -3 + 1/2*ToReal(N))))

```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `UNSAT` result indicates that for *every* possible loop bound, there is no data configuration that forces sequentiality. This strongly implies the loop is Not DOFS (parallelizable) across all valid loop bounds.

---

#### `test_gauss_seidel_traditional_dofs`

#### Pseudocode

```

// Traditional 1D Gauss-Seidel
for i = 1 to N-1:
  A[i] = A[i-1] + A[i+1]

```

#### Description

This loop is inherently sequential due to a Read-After-Write (RAW) dependency where `A[i]` depends on `A[i-1]` from the current iteration.

#### Expected Outcome

**Traditional 1D Gauss-Seidel ( `gauss_seidel_traditional_dofs` )**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

#### SMT Analysis

##### `gauss_seidel_traditional_dofs.smt2`

```

DATA!A == 10001
3 <= N
True

--- Model (Witness) ---
N = 3
DATA!A = 10001

```

*Interpretation*: This SMT query attempts to find a data configuration (including loop bounds as data) that forces a dependency between adjacent iterations. The `SAT` result indicates that such a data configuration (and loop bound, e.g., `N=3` ) exists, making the loop fully sequential (DOFS).

#### `test_gauss_seidel_traditional_dofs_forall_bounds`

#### Pseudocode

```

// Traditional 1D Gauss-Seidel
for i = 1 to N-1:
  A[i] = A[i-1] + A[i+1]

```

#### Description

Analyzes the same loop logic as `test_gauss_seidel_traditional_dofs` , but using loop bounds SMT generation. This loop is inherently sequential due to a Read-After-Write (RAW) dependency where `A[i]` depends on `A[i-1]` from the current iteration.

#### Expected Outcome

**Traditional 1D Gauss-Seidel ( `gauss_seidel_traditional_dofs_forall_bounds` )**: DOFS (Sequential). SMT query returns SAT, proving that a data configuration exists that forces sequentiality.

#### SMT Analysis

##### `gauss_seidel_traditional_dofs_forall_bounds.smt2`

```

DATA!A == 10001
3 <= N
True

--- Model (Witness) ---
N = 3
DATA!A = 10001

```

*Interpretation*: This query universally quantifies `N` (loop bounds) and attempts to find a data configuration that forces a dependency. The `SAT` result indicates that for *every* possible loop bound, there exists a data configuration that forces sequentiality. This means the loop is DOFS (sequential) for all loop bounds.

---
