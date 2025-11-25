# P3G Pseudocode Syntax (`.pcode`)

This document outlines the syntax for the `.pcode` pseudocode language used to define Program-level Dependence Graphs (P3G). The syntax is designed to be a simple, human-readable way to describe computations, data accesses, and control flow, which can then be parsed into a formal P3G model for dependency analysis.

## Table of Contents

1.  [Overview](#overview)
2.  [File Structure](#file-structure)
    -   [Declarations (`decl`, `sym`, `var`)](#declarations-decl-sym-var)
    -   [Output Specification (`out`)](#output-specification-out)
    -   [Statements](#statements)
3.  [Statement Syntax](#statement-syntax)
    -   [Access Annotations](#access-annotations)
    -   [Dataflow Specification](#dataflow-specification)
    -   [Statement Naming](#statement-naming)
4.  [Statement Types](#statement-types)
    -   [Compute (`op`)](#compute-op)
    -   [Sequential Loop (`for`)](#sequential-loop-for)
    -   [Conditional (`if-else`)](#conditional-if-else)
    -   [Assertion (`!`)](#assertion-)
5.  [Access Patterns](#access-patterns)
    -   [Single Element](#single-element)
    -   [Range](#range)
    -   [Multi-dimensional](#multi-dimensional)
    -   [Inferred Access (`?`)](#inferred-access-)
6.  [Expressions](#expressions)
7.  [Full Examples](#full-examples)
    -   [Example 1: Sequential Loop](#example-1-sequential-loop)
    -   [Example 2: Data-Aware Branch](#example-2-data-aware-branch)
    -   [Example 3: Explicit Dataflow](#example-3-explicit-dataflow)

---

## Overview

A `.pcode` file consists of two main parts:
1.  **Declarations**: Global declarations of all arrays and specification of which arrays are outputs.
2.  **Statements**: A series of computational steps described using a specific statement syntax that makes data dependencies explicit.

The language is indentation-sensitive, similar to Python.

## File Structure

### Declarations (`decl`, `sym`, `var`)

All arrays, symbolic constants, and loop variables must be declared at the beginning of the file.

#### Array Declarations (`decl`)
All arrays (or data containers) must be declared using the `decl` keyword.

**Syntax:**
```
decl <array1>, <array2>, ...
```

**Example:**
```pcode
decl A, B, C
```

#### Symbolic Constant Declarations (`sym`)
Symbolic constants, such as loop bounds or other parameters, must be declared using the `sym` keyword. These are treated as immutable inputs to the program.

**Syntax:**
```
sym <symbol1>, <symbol2>, ...
```

**Example:**
```pcode
sym N, M
```

#### Loop Variable Declarations (`var`)
All variables that will be used as iterators in `for` loops must be declared using the `var` keyword.

**Syntax:**
```
var <variable1>, <variable2>, ...
```

**Example:**
```pcode
var i, j, k
```

### Output Specification (`out`)

You must specify which arrays are considered outputs of the program. This is crucial for certain types of dependency analysis.

**Syntax:**
```
out <array1>, <array2>, ...
```

**Example:**
```pcode
decl A, B
out A
```

### Statements

The body of the program consists of a sequence of statements. Each statement is defined by its data accesses (reads and writes) and the operation it performs (e.g., a loop, a conditional branch, or a generic computation).

---

## Statement Syntax

The core of the language is its unique statement syntax, which explicitly annotates the dataflow and dependencies.

**General Form:**
```
(<reads>) => (<writes>) (<source_states>).<statement_name>| <statement_body>
```

Let's break this down:

### 1. Access Annotations

-   `(<reads>)`: A comma-separated list of arrays and their accessed subsets that the statement reads from.
-   `=>`: An arrow separating the read set from the write set.
-   `(<writes>)`: A comma-separated list of arrays and their subsets that the statement writes to.

**Example:**
```pcode
(A[i-1], B[i]) => (A[i])
```
This annotation declares that the statement reads from `A[i-1]` and `B[i]` to produce a new value for `A[i]`.

### 2. Dataflow Specification

This part explicitly defines the data dependencies between statements.

-   `(<source_states>)`: Optional. A comma-separated list of the names of previous statements. The data read by the current statement will be sourced from the versions produced by these specified source statements.
-   `.`: A dot separating the source states from the current statement's name.
-   If `(<source_states>)` is omitted (e.g., `.S1|`), the statement depends on the initial state of the arrays.
-   If the entire dataflow specification is omitted, the statement is assumed to depend on the lexically preceding statement.

### 3. Statement Naming

-   `<statement_name>|`: A unique name for the current statement, followed by a pipe `|`. This name is used to identify the state of the data after this statement completes and can be referenced in the `(<source_states>)` of subsequent statements.
-   Anonymous statements are also possible by omitting the name (e.g., `| for ...`).

---

## Statement Types

The `<statement_body>` can be one of the following types.

### Compute (`op`)

Represents a generic, atomic computation. The details of the computation are considered a black box, but its data accesses are fully defined by the annotation.

**Syntax:**
```
(<reads>) => (<writes>) S1| op(description)
```

**Example:**
```pcode
decl A, B

(A[i-1], B[i]) => (A[i]) S1| op(add)
```

### Sequential Loop (`for`)

Represents a sequential `for` loop. The loop body is an indented block of further statements.

**Syntax:**
```
(<reads>) => (<writes>) L1| for <var> = <start> to <end>:
    <indented_block_of_statements>
```
- `<var>`: The loop iteration variable.
- `<start>` and `<end>`: Expressions defining the inclusive loop bounds.

**Example:**
```pcode
decl A, B

(A[0:N-1], B[1:N]) => (A[1:N]) L1| for i = 1 to N:
    (A[i-1], B[i]) => (A[i]) S1| op(add)
```
Here, the loop `L1` as a whole reads from `A[0:N-1]` and `B[1:N]` and writes to `A[1:N]`. The statement `S1` inside the loop specifies the access for a single iteration.

### Conditional (`if-else`)

Represents a conditional branch.

**Syntax:**
```
(<reads>) => (<writes>) B1| if <condition>:
    <indented_if_block>
else:
    <indented_else_block>
```
- `<condition>`: A boolean expression, e.g., `B[i] > 0`.
- The `else` block is optional.

**Example:**
```pcode
decl A, B

(A[0:N-1], B[1:N]) => (A[1:N]) B1| if B[i] > 0:
    (A[i-1]) => (A[i]) S2| op(copy)
```

### Assertion (`!`)

Represents a precise assertion about the program state. This is not a computational statement but a declaration that a certain condition must hold. Assertions are specified on a line starting with `!`.

**Syntax:**
```
! <condition>
```
The condition can also be enclosed in parentheses for clarity:
```
! (<condition>)
```

- `<condition>`: A boolean expression, e.g., `N > 0`.

**Example:**
```pcode
decl A
out A

! (N > 0)

() => (A[0]) S1| op(init)

(A[0:N-1]) => (A[1:N]) L1| for i = 1 to N:
    (A[i-1]) => (A[i]) S2| op(step)
```

In this example, `! (N > 0)` asserts that the symbol `N` is positive before the loop begins. These assertions can be used by backend analysis tools to verify properties or optimize the program representation.

---

## Access Patterns

The language supports several ways to describe the subset of an array being accessed.

### Single Element
Accessing a single element at a specific index.
- `A[i]`
- `A[i+1]`

### Range
Accessing a contiguous range of elements, inclusive.
- `A[0:N-1]` (accesses elements from 0 to N-1)

### Multi-dimensional
Combining patterns for multi-dimensional arrays, separated by commas.
- `C[i, j]`
- `C[i, 0:N]`

### Inferred Access (`?`)
Using a question mark `?` indicates that the exact access pattern is unknown and should be inferred by an analysis engine. This is useful for complex access patterns that are hard to express statically.
- `A[?]`

---

## Expressions

Expressions can be used in loop bounds, access indices, and `if` conditions. They support:
- **Literals**: `1`, `42`
- **Variables**: Loop variables (`i`) or globally defined symbols (`N`).
- **Arithmetic**: `+`, `-`, `*`.
- **Array Reads**: `A[i]`, `B[i-1]` (only for reading a value within a condition or another expression, not for defining the statement's primary access annotation).

---

## Full Examples

### Example 1: Sequential Loop
A simple sequential loop where each element depends on the previous one.

```pcode
decl A, B
out A

(A[0:N-1], B[1:N]) => (A[1:N]) L1| for i = 1 to N:
    () => () S1| op(some_op)
```
_Note: In this simplified example, we omit the inner statement's accesses, assuming they are inferred._

### Example 2: Data-Aware Branch
A loop where a write only occurs if a condition is met.

```pcode
decl A, B
out A

(A[0:N-1], B[1:N]) => (A[1:N]) L1| for i = 1 to N:
    (B[i]) => () B1| if B[i] > 0:
        (A[i-1]) => (A[i]) S1| op(copy)
```
- The `if` statement `B1` only *reads* `B[i]` to evaluate its condition.
- The `op` statement `S1` only executes if the branch is taken.

### Example 3: Explicit Dataflow
Two sequential operations where the second (`S2`) explicitly depends on the data state produced by the first (`S1`).

```pcode
decl A, B, C
out C

(A[?]) => (B[?]) S1| op(step1)

(B[?]) => (C[?]) (S1).S2| op(step2)
```
- `S2` reads the version of `B` that was written by `S1`.
