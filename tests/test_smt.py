import logging

from pysmt.shortcuts import Symbol, INT, Plus, Int, GE, LE, ArrayType, Store, Select

from p3g.p3g import GraphBuilder
from p3g.smt import generate_smt_for_disprove_dofs
from p3g.smt import generate_smt_for_prove_exists_data_forall_iter_isdep


# Helper to create a simple P3G loop for testing
# Represents a program like:
# for i in range(0, N):
#   B[i] = A[i]
def build_simple_loop_graph():
    builder = GraphBuilder()
    i = builder.add_symbol("i")
    N = builder.add_symbol("N")
    A = builder.add_data("A")
    B = builder.add_data("B")

    with builder.add_loop("loop1", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]) as loop:
        builder.add_compute("comp1", reads=[(A, i)], writes=[(B, i)])

    return builder.root_graph, loop, i, N, A, B


# Helper to build a graph with a branch
# Represents a program like:
# for i in range(0, N):
#   if x >= 0:
#     B[i] = A[i]
#   else: # x <= 0
#     C[i] = A[i+1]
def build_branch_graph():
    builder = GraphBuilder()
    i = builder.add_symbol("i")
    N = builder.add_symbol("N")
    x = builder.add_symbol("x")
    A = builder.add_data("A")
    B = builder.add_data("B")
    C = builder.add_data("C")

    with builder.add_loop("loop1", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]) as loop:
        with builder.add_branch("branch1", reads=[], writes=[]) as branch:
            with branch.add_path(GE(x, Int(0))):
                builder.add_compute("comp_true", reads=[(A, i)], writes=[(B, i)])
            with branch.add_path(LE(x, Int(0))):
                builder.add_compute("comp_false", reads=[(A, Plus(i, Int(1)))], writes=[(C, i)])
    return builder.root_graph, loop, i, N, x, A, B, C


class TestSmtGeneration:
    def test_generate_smt_for_disprove_dofs_simple_loop(self):
        root_graph, loop, i, N, A, B = build_simple_loop_graph()

        smt_query = generate_smt_for_disprove_dofs(loop, N)

        # Check for declarations
        assert "(declare-fun N () Int)" in smt_query
        assert "(declare-fun DATA!A () Int)" in smt_query
        assert "(declare-fun DATA!B () Int)" in smt_query
        assert "(declare-fun i () Int)" in smt_query

        # Check for data definitions
        assert "(assert (= DATA!A 10001))" in smt_query
        assert "(assert (= DATA!B 10002))" in smt_query

        # Check for loop bounds
        assert "(assert (<= (+ 0 1) N))" in smt_query
        assert "(assert (<= 0 i))" in smt_query
        assert "(assert (<= (+ i 1) N))" in smt_query

        # Check for dependency logic
        assert "; Find a universal counterexample (for all data configs)" in smt_query
        assert "(assert (let (" in smt_query
        assert "(p0p0_dep (and" in smt_query
        assert "(not (or" in smt_query
        assert "p0p0_dep" in smt_query

        # DOFS should not have forall quantifiers for data arrays if they are not used as functions
        assert "(forall" not in smt_query

    def test_generate_smt_for_disprove_dofs_with_array_data(self):
        # Represents a program like:
        # declare A_arr: Array[Int, Int]
        # for i in range(0, N):
        #   # Read from A_arr[i]
        #   # Write to A_arr[i] = 0
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        # Define A as an array
        A_array_sym = Symbol("A_arr", ArrayType(INT, INT))
        A = builder.add_data("A")  # This will still create a DATA!A symbol

        # Simulate an array access in a compute node
        with builder.add_loop("loop1", "i", Int(0), N, reads=[(A, Select(A_array_sym, i))],
                              writes=[(A, Store(A_array_sym, i, Int(0)))]) as loop:
            builder.add_compute("comp1", reads=[(A, Select(A_array_sym, i))],
                                writes=[(A, Store(A_array_sym, i, Int(0)))])

        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop, N)

        # Check for declarations
        assert "(declare-fun A_arr () (Array Int Int))" in smt_query  # Array declaration
        assert "(declare-fun DATA!A () Int)" in smt_query  # Still have the data ID symbol

        # Check for exists quantifier for data arrays
        assert "(exists (" in smt_query
        assert "(A_arr (Array Int Int))" in smt_query
        assert "(DATA!A Int)" in smt_query
        assert ") ; End of existential variables" in smt_query

        # Check for forall quantifier for iteration variable
        assert "(forall (" in smt_query
        assert "(i Int)" in smt_query
        assert ") ; End of universal variables" in smt_query

    def test_generate_smt_for_disprove_dofs_with_extra_assertions(self):
        root_graph, loop, i, N, A, B = build_simple_loop_graph()

        extra_assertion = GE(N, Int(10))
        smt_query = generate_smt_for_disprove_dofs(loop, N, extra_assertions=[extra_assertion])

        assert "; Human Assertion #0" in smt_query
        assert "(assert (<= 10 N))" in smt_query


class TestProveExistsDataForallIterIsdep:
    def test_simple_loop(self):
        root_graph, loop, i, N, A, B = build_simple_loop_graph()

        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop, N)
        print(f"""
{smt_query}
""")

        # Check for declarations
        assert "(declare-fun N () Int)" in smt_query
        assert "(declare-fun DATA!A () Int)" in smt_query
        assert "(declare-fun DATA!B () Int)" in smt_query
        assert "(declare-fun i () Int)" in smt_query

        # Check for data definitions (these are still global assertions)
        assert "(assert (= DATA!A 10001))" in smt_query
        assert "(assert (= DATA!B 10002))" in smt_query

        # Check for quantifiers
        assert "(forall (" in smt_query
        assert "(i Int)" in smt_query

        # Check for loop bounds and dependency logic within the quantified formula
        assert "(let (" in smt_query
        assert "(p0p0_dep (and" in smt_query
        assert "(and" in smt_query # The main AND combining loop bounds and dependency
        assert "(<= (+ 0 1) N)" in smt_query # loop_runs_at_least_two_iterations
        assert "(<= 0 i)" in smt_query       # k_lower_bound
        assert "(<= (+ i 1) N)" in smt_query # j_upper_bound
        assert "(or" in smt_query           # main_body_str (dependency)
        assert "p0p0_dep" in smt_query

        # Ensure no "not" for the main dependency
        assert "(not (or" not in smt_query

    def test_with_array_data(self):
        # Represents a program like:
        # declare A_arr: Array[Int, Int]
        # for i in range(0, N):
        #   # Read from A_arr[i]
        #   # Write to A_arr[i] = 0
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        # Define A as an array
        A_array_sym = Symbol("A_arr", ArrayType(INT, INT))
        A = builder.add_data("A")  # This will still create a DATA!A symbol

        # Simulate an array access in a compute node
        with builder.add_loop("loop1", "i", Int(0), N, reads=[(A, Select(A_array_sym, i))],
                              writes=[(A, Store(A_array_sym, i, Int(0)))]) as loop:
            builder.add_compute("comp1", reads=[(A, Select(A_array_sym, i))],
                                writes=[(A, Store(A_array_sym, i, Int(0)))])

        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop, N)
        print(f"""
{smt_query}
""")

        # Check for declarations
        assert "(declare-fun A_arr () (Array Int Int))" in smt_query  # Array declaration
        assert "(declare-fun DATA!A () Int)" in smt_query  # Still have the data ID symbol

        # Check for forall quantifier for iteration variable
        assert "(forall (" in smt_query
        assert "(i Int)" in smt_query
        assert ") ; End of universal variables" in smt_query

    def test_with_extra_assertions(self):
        root_graph, loop, i, N, A, B = build_simple_loop_graph()

        extra_assertion = GE(N, Int(10))
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop, N, extra_assertions=[extra_assertion])
        print(f"""
{smt_query}
""")

        assert "; Human Assertion #0" in smt_query
        assert "(assert (<= 10 N))" in smt_query
