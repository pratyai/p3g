import io

from pysmt.shortcuts import Symbol, INT, Plus, Int, GE, LE, ArrayType, Store, Select, Equals
from pysmt.smtlib.parser import SmtLibParser
from pysmt.walkers import IdentityDagWalker

from p3g.p3g import GraphBuilder
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


class SmtQueryInspector(IdentityDagWalker):
    """
    A PySMT walker to inspect the structure of the parsed SMT query.
    """
    def __init__(self, env=None):
        IdentityDagWalker.__init__(self, env)
        self.declarations = []
        self.assertions = []
        self.quantifiers = []
        self.let_bindings = []

    def walk_assert(self, formula):
        self.assertions.append(formula) # Append the formula directly
        return formula

    # Removed walk_declare_fun as it's handled directly in parse_smt_query_and_inspect

    def walk_forall(self, formula):
        self.quantifiers.append(('forall', formula.quantifier_vars(), formula.arg(0)))
        return formula

    def walk_exists(self, formula):
        self.quantifiers.append(('exists', formula.quantifier_vars(), formula.arg(0)))
        return formula

    def walk_let(self, formula):
        # PySMT's internal representation of LET is a bit tricky.
        # For now, we'll just note its presence.
        self.let_bindings.append(formula)
        return formula


def parse_smt_query_and_inspect(smt_query_string: str):
    """
    Parses an SMT-LIB query string and returns an inspector object
    that can be used to assert properties of the parsed query.
    """
    parser = SmtLibParser()
    script = parser.get_script(io.StringIO(smt_query_string))

    inspector = SmtQueryInspector()
    for cmd in script.commands:
        if cmd.name == "assert":
            inspector.walk_assert(cmd.args[0])
        elif cmd.name == "declare-fun":
            # Assume cmd.args[0] is the symbol name (string)
            # Assume cmd.args[-1] is the type (PySMT Type object)
            inspector.declarations.append(cmd)
        elif cmd.name == "check-sat":
            pass # Ignore check-sat command for inspection
        else:
            # Optionally raise an error or log a warning for unhandled commands
            pass
    # Manually walk the assertions to find quantifiers and let bindings
    # We need to walk the actual formulas, not the commands
    for assertion_formula in inspector.assertions:
        # Use a fresh inspector for each assertion to avoid mixing state
        # Or, modify SmtQueryInspector to be a proper walker that can be called on sub-formulas
        # For now, let's just walk the top-level assertions and extract quantifiers/lets from them
        # This is a simplified approach. A full walker would be more complex.
                    if assertion_formula.is_forall():
                        inspector.walk_forall(assertion_formula)
                    elif assertion_formula.is_exists():
                        inspector.walk_exists(assertion_formula)
    return inspector


class TestProveExistsDataForallIterIsdep:
    def test_simple_loop(self):
        root_graph, loop, i, N, A, B = build_simple_loop_graph()

        smt_query_string = generate_smt_for_prove_exists_data_forall_iter_isdep(loop, N)
        inspector = parse_smt_query_and_inspect(smt_query_string)

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {
            "N",
            "DATA!A",
            "DATA!B",
            "i"
        }
        declared_symbols = {cmd.args[0].symbol_name() for cmd in inspector.declarations if cmd.name == "declare-fun"}
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
            (Symbol("DATA!B", INT), Int(10002))
        }
        # Check if these specific assertions are present in the inspector's assertions
        found_data_assertions_args = set()
        for assertion_formula in inspector.assertions:
            if assertion_formula.is_equals() and \
               assertion_formula.arg(0).is_symbol() and \
               assertion_formula.arg(0).symbol_name().startswith("DATA!"):
                found_data_assertions_args.add((assertion_formula.arg(0), assertion_formula.arg(1)))

        for expected_arg0, expected_arg1 in data_id_assertions:
            assert (expected_arg0, expected_arg1) in found_data_assertions_args, \
                f"Expected assertion (= {expected_arg0} {expected_arg1}) not found."

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == 'forall'
        assert len(q_vars) == 1
        assert q_vars[0] == Symbol("i", INT)

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        main_assertion_body = q_body
        assert main_assertion_body.is_implies() # (=> A B)
        loop_bounds_formula = main_assertion_body.arg(0)
        dependency_let_formula = main_assertion_body.arg(1)

        # Check loop bounds
        assert loop_bounds_formula.is_and()
        assert GE(N, Plus(Int(0), Int(1))) in loop_bounds_formula.args() # (<= (+ 0 1) N)
        assert GE(Symbol("i", INT), Int(0)) in loop_bounds_formula.args() # (<= 0 i)
        assert LE(Plus(Symbol("i", INT), Int(1)), N) in loop_bounds_formula.args() # (<= (+ i 1) N)

        # Check dependency logic by looking for key substrings in the SMT query string
        assert "(and (= DATA!B DATA!B) (= i (+ i 1)))" in smt_query_string # WAW
        assert "(or (and (= DATA!B DATA!A) (= i (+ i 1))) (and (= DATA!B DATA!B) (= i (+ i 1))))" in smt_query_string # RAW
        assert "(or (and (= DATA!A DATA!B) (= i (+ i 1))) (and (= DATA!B DATA!B) (= i (+ i 1))))" in smt_query_string # WAR

        # Ensure no "not" for the main dependency
        # The overall structure should be (forall (i) (=> loop_bounds (let (...) (or ...))))
        # We are proving existence of dependency, so no top-level NOT.
        assert not any(a.is_not() for a in inspector.assertions)

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

        assert "; Human Assertion #0" in smt_query
        assert "(assert (<= 10 N))" in smt_query
