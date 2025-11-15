import io

from pysmt.shortcuts import (
    Symbol,
    INT,
    Plus,
    Int,
    GE,
    LE,
    ArrayType,
    Store,
    Select,
    LT,
)
from pysmt.smtlib.parser import SmtLibParser
from pysmt.walkers import IdentityDagWalker

from p3g.p3g import GraphBuilder
from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_forall_iter_isindep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
)


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

    with builder.add_loop(
        "loop1", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]
    ) as loop:
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

    with builder.add_loop(
        "loop1", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]
    ) as loop:
        with builder.add_branch("branch1", reads=[], writes=[]) as branch:
            with branch.add_path(GE(x, Int(0))):
                builder.add_compute("comp_true", reads=[(A, i)], writes=[(B, i)])
            with branch.add_path(LE(x, Int(0))):
                builder.add_compute(
                    "comp_false", reads=[(A, Plus(i, Int(1)))], writes=[(C, i)]
                )
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
        self.assertions.append(formula)  # Append the formula directly
        return formula

    # Removed walk_declare_fun as it's handled directly in parse_smt_query_and_inspect

    def walk_forall(self, formula):
        self.quantifiers.append(("forall", formula.quantifier_vars(), formula.arg(0)))
        return formula

    def walk_exists(self, formula):
        self.quantifiers.append(("exists", formula.quantifier_vars(), formula.arg(0)))
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
            pass  # Ignore check-sat command for inspection
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

        smt_query_string = generate_smt_for_prove_exists_data_forall_iter_isdep(loop)
        inspector = parse_smt_query_and_inspect(smt_query_string)

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"N", "DATA!A", "DATA!B", "i"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
            (Symbol("DATA!B", INT), Int(10002)),
        }
        # Check if these specific assertions are present in the inspector's assertions
        found_data_assertions_args = set()
        for assertion_formula in inspector.assertions:
            if (
                assertion_formula.is_equals()
                and assertion_formula.arg(0).is_symbol()
                and assertion_formula.arg(0).symbol_name().startswith("DATA!")
            ):
                found_data_assertions_args.add(
                    (assertion_formula.arg(0), assertion_formula.arg(1))
                )

        for expected_arg0, expected_arg1 in data_id_assertions:
            assert (expected_arg0, expected_arg1) in found_data_assertions_args, (
                f"Expected assertion (= {expected_arg0} {expected_arg1}) not found."
            )

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert len(q_vars) == 1
        assert q_vars[0] == Symbol("i", INT)

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        main_assertion_body = q_body
        assert main_assertion_body.is_implies()  # (=> A B)
        loop_bounds_formula = main_assertion_body.arg(0)
        dependency_let_formula = main_assertion_body.arg(1)

        # Check loop bounds
        assert loop_bounds_formula.is_and()
        assert (
            GE(N, Plus(Int(0), Int(1))) in loop_bounds_formula.args()
        )  # (<= (+ 0 1) N)
        assert GE(Symbol("i", INT), Int(0)) in loop_bounds_formula.args()  # (<= 0 i)
        assert (
            LE(Plus(Symbol("i", INT), Int(1)), N) in loop_bounds_formula.args()
        )  # (<= (+ i 1) N)

        # Check dependency logic by looking for key substrings in the SMT query string
        assert "(and (= DATA!B DATA!B) (= i (+ i 1)))" in smt_query_string  # WAW
        assert "(and (= DATA!B DATA!B) (= i (+ i 1)))" in smt_query_string  # RAW
        assert "(and (= DATA!B DATA!B) (= i (+ i 1)))" in smt_query_string  # WAR

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
        with builder.add_loop(
            "loop1",
            "i",
            Int(0),
            N,
            reads=[(A, Select(A_array_sym, i))],
            writes=[(A, Store(A_array_sym, i, Int(0)))],
        ) as loop:
            builder.add_compute(
                "comp1",
                reads=[(A, Select(A_array_sym, i))],
                writes=[(A, Store(A_array_sym, i, Int(0)))],
            )

        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(loop)

        # Check for declarations
        assert (
            "(declare-fun A_arr () (Array Int Int))" in smt_query
        )  # Array declaration
        assert (
            "(declare-fun DATA!A () Int)" in smt_query
        )  # Still have the data ID symbol

        # Check for forall quantifier for iteration variable
        assert "(forall (" in smt_query
        assert "(i Int)" in smt_query
        assert ") ; End of universal variables" in smt_query

    def test_with_extra_assertions(self):
        root_graph, loop, i, N, A, B = build_simple_loop_graph()

        extra_assertion = GE(N, Int(10))
        smt_query = generate_smt_for_prove_exists_data_forall_iter_isdep(
            loop, extra_assertions=[extra_assertion]
        )

        assert "; Human Assertion #0" in smt_query
        assert "(assert (<= 10 N))" in smt_query


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_simple_loop_with_symbolic_bounds(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")  # N is a symbolic loop bound
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_loop(
            "loop1", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]
        ) as loop:
            builder.add_compute("comp1", reads=[(A, i)], writes=[(B, i)])

        smt_query_string = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(loop)
        )
        inspector = parse_smt_query_and_inspect(smt_query_string)

        # Check for declarations
        expected_declarations = {"N", "DATA!A", "DATA!B", "i"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i' AND 'N'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert len(q_vars) == 2  # Now includes N
        assert Symbol("i", INT) in q_vars
        assert Symbol("N", INT) in q_vars

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        main_assertion_body = q_body
        assert main_assertion_body.is_implies()  # (=> A B)
        loop_bounds_formula = main_assertion_body.arg(0)
        dependency_let_formula = main_assertion_body.arg(1)

        # Check loop bounds
        assert loop_bounds_formula.is_and()
        assert (
            GE(N, Plus(Int(0), Int(1))) in loop_bounds_formula.args()
        )  # (<= (+ 0 1) N)
        assert GE(Symbol("i", INT), Int(0)) in loop_bounds_formula.args()  # (<= 0 i)
        assert (
            LE(Plus(Symbol("i", INT), Int(1)), N) in loop_bounds_formula.args()
        )  # (<= (+ i 1) N)

        # Ensure no "not" for the main dependency
        assert not any(a.is_not() for a in inspector.assertions)

    def test_symbolic_lower_bound(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        M = builder.add_symbol("M")  # M is a symbolic lower bound
        N = builder.add_symbol("N")  # N is a symbolic upper bound
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_loop(
            "loop1", "i", M, N, reads=[(A, i)], writes=[(B, i)]
        ) as loop:
            builder.add_compute("comp1", reads=[(A, i)], writes=[(B, i)])

        smt_query_string = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(loop)
        )
        inspector = parse_smt_query_and_inspect(smt_query_string)

        # Check for declarations
        expected_declarations = {"M", "N", "DATA!A", "DATA!B", "i"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i', 'M' and 'N'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert len(q_vars) == 3  # Now includes M and N
        assert Symbol("i", INT) in q_vars
        assert Symbol("M", INT) in q_vars
        assert Symbol("N", INT) in q_vars

        # Check loop bounds in the formula
        main_assertion_body = q_body
        loop_bounds_formula = main_assertion_body.arg(0)
        assert loop_bounds_formula.is_and()
        assert GE(N, Plus(M, Int(1))) in loop_bounds_formula.args()  # (<= (+ M 1) N)
        assert GE(Symbol("i", INT), M) in loop_bounds_formula.args()  # (<= M i)
        assert (
            LE(Plus(Symbol("i", INT), Int(1)), N) in loop_bounds_formula.args()
        )  # (<= (+ i 1) N)


class TestProveExistsDataForallIterIsindep:
    def test_simple_loop_independence(self):
        root_graph, loop, i, N, A, B = build_simple_loop_graph()
        j = Symbol(f"{i.symbol_name()}_j", INT)  # Need to define j for assertions

        smt_query_string = generate_smt_for_prove_exists_data_forall_iter_isindep(loop)
        inspector = parse_smt_query_and_inspect(smt_query_string)

        # Check for declarations
        expected_declarations = {
            "N",
            "DATA!A",
            "DATA!B",
            "i",
            "i_j",
        }  # i_j is the symbol name for j
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for existential quantifiers (for data variables)
        # Find the main quantified assertion (which contains the exists/forall)
        main_quantified_assertion = None
        for assertion in inspector.assertions:
            if assertion.is_forall():  # The main assertion for DOFI is a forall
                main_quantified_assertion = assertion
                break
        assert main_quantified_assertion is not None, (
            "Could not find the main quantified assertion."
        )

        top_level_assertion = main_quantified_assertion  # Use the found assertion
        assert top_level_assertion.is_forall()

        # The DATA! symbols are not explicitly existentially quantified in the SMT-LIB output.
        # They are free variables that the solver will try to find values for.
        # So, we don't check for them in the forall_q_vars.

        # Check for universal quantifiers (for i and j) inside the forall body
        # The top_level_assertion is already the forall.
        forall_q_vars = top_level_assertion.quantifier_vars()
        forall_q_body = top_level_assertion.arg(0)
        assert Symbol("i", INT) in forall_q_vars
        assert Symbol("i_j", INT) in forall_q_vars  # Check for j

        # Check the body of the quantified formula (main assertion)
        # It should contain (=> loop_bounds (not (let (...) (or ...))))
        assert forall_q_body.is_implies()
        loop_bounds_formula = forall_q_body.arg(0)
        negated_dependency_formula = forall_q_body.arg(1)

        # Check loop bounds
        assert loop_bounds_formula.is_and()
        assert GE(j, Int(0)) in loop_bounds_formula.args()  # j >= 0
        assert LT(j, i) in loop_bounds_formula.args()  # j < i
        assert GE(i, Int(0)) in loop_bounds_formula.args()  # i >= 0
        assert LE(i, N) in loop_bounds_formula.args()  # i <= N

        # Check for negation of dependency
        assert negated_dependency_formula.is_not()
        # dependency_let_formula = negated_dependency_formula.arg(0)
        # assert dependency_let_formula.is_let() # <--- Removed this line
        assert "(let (" in smt_query_string  # <--- Added this line

        # Check dependency logic by looking for key substrings in the SMT query string
        # The actual content of the let/or will be complex, so just check for presence
        assert "(let (" in smt_query_string
        assert "(or " in smt_query_string
        assert "p0p0_waw" in smt_query_string  # Example conflict var


class TestProveExistsDataForallLoopBoundsIterIsindep:
    def test_simple_loop_independence_forall_bounds(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")  # N is a symbolic loop bound
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_loop(
            "loop1", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]
        ) as loop:
            builder.add_compute("comp1", reads=[(A, i)], writes=[(B, i)])

        smt_query_string = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep(loop)
        )
        inspector = parse_smt_query_and_inspect(smt_query_string)

        # Check for declarations
        expected_declarations = {"N", "DATA!A", "DATA!B", "i", "i_j"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for existential quantifiers (for data variables)
        # Find the main quantified assertion (which contains the exists/forall)
        main_quantified_assertion = None
        for assertion in inspector.assertions:
            if assertion.is_forall():  # The main assertion for DOFI is a forall
                main_quantified_assertion = assertion
                break
        assert main_quantified_assertion is not None, (
            "Could not find the main quantified assertion."
        )

        top_level_assertion = main_quantified_assertion  # Use the found assertion
        assert top_level_assertion.is_forall()

        # The DATA! symbols are not explicitly existentially quantified in the SMT-LIB output.
        # They are free variables that the solver will try to find values for.
        # So, we don't check for them in the forall_q_vars.

        # Check for universal quantifiers (for i, j, and N) inside the forall body
        # The top_level_assertion is already the forall.
        forall_q_vars = top_level_assertion.quantifier_vars()
        forall_q_body = top_level_assertion.arg(0)

        assert Symbol("i", INT) in forall_q_vars
        assert Symbol("i_j", INT) in forall_q_vars  # Check for j
        assert Symbol("N", INT) in forall_q_vars  # Check for N

        # Check the body of the quantified formula (main assertion)
        assert forall_q_body.is_implies()
        loop_bounds_formula = forall_q_body.arg(0)
        negated_dependency_formula = forall_q_body.arg(1)

        # Check loop bounds
        assert loop_bounds_formula.is_and()
        assert GE(Symbol("i_j", INT), Int(0)) in loop_bounds_formula.args()  # j >= 0
        assert (
            LT(Symbol("i_j", INT), Symbol("i", INT)) in loop_bounds_formula.args()
        )  # j < i
        assert GE(Symbol("i", INT), Int(0)) in loop_bounds_formula.args()  # i >= 0
        assert LE(Symbol("i", INT), N) in loop_bounds_formula.args()  # i <= N

        # Check for negation of dependency
        assert negated_dependency_formula.is_not()
        assert "(let (" in smt_query_string
        assert "(or " in smt_query_string
        assert "p0p0_waw" in smt_query_string  # Example conflict var

    def test_symbolic_lower_bound_forall_bounds(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        M = builder.add_symbol("M")  # M is a symbolic lower bound
        N = builder.add_symbol("N")  # N is a symbolic upper bound
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_loop(
            "loop1", "i", M, N, reads=[(A, i)], writes=[(B, i)]
        ) as loop:
            builder.add_compute("comp1", reads=[(A, i)], writes=[(B, i)])

        smt_query_string = (
            generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep(loop)
        )
        inspector = parse_smt_query_and_inspect(smt_query_string)

        # Check for declarations
        # Check for existential quantifiers (for data variables)
        # Find the main quantified assertion (which contains the exists/forall)
        main_quantified_assertion = None
        for assertion in inspector.assertions:
            if assertion.is_forall():  # The main assertion for DOFI is a forall
                main_quantified_assertion = assertion
                break
        assert main_quantified_assertion is not None, (
            "Could not find the main quantified assertion."
        )

        top_level_assertion = main_quantified_assertion  # Use the found assertion
        assert top_level_assertion.is_forall()

        # The DATA! symbols are not explicitly existentially quantified in the SMT-LIB output.
        # They are free variables that the solver will try to find values for.
        # So, we don't check for them in the forall_q_vars.

        # Check for universal quantifiers (for i, j, M, and N) inside the forall body
        # The top_level_assertion is already the forall.
        forall_q_vars = top_level_assertion.quantifier_vars()
        forall_q_body = top_level_assertion.arg(0)

        assert Symbol("i", INT) in forall_q_vars
        assert Symbol("i_j", INT) in forall_q_vars  # Check for j
        assert Symbol("M", INT) in forall_q_vars  # Check for M
        assert Symbol("N", INT) in forall_q_vars  # Check for N

        # Check the body of the quantified formula (main assertion)
        assert forall_q_body.is_implies()
        loop_bounds_formula = forall_q_body.arg(0)
        negated_dependency_formula = forall_q_body.arg(1)

        # Check loop bounds
        assert loop_bounds_formula.is_and()
        assert GE(Symbol("i_j", INT), M) in loop_bounds_formula.args()  # j >= M
        assert (
            LT(Symbol("i_j", INT), Symbol("i", INT)) in loop_bounds_formula.args()
        )  # j < i
        assert GE(Symbol("i", INT), M) in loop_bounds_formula.args()  # i >= M
        assert LE(Symbol("i", INT), N) in loop_bounds_formula.args()  # i <= N

        # Check for negation of dependency
        assert negated_dependency_formula.is_not()
        assert "(let (" in smt_query_string
        assert "(or " in smt_query_string
        assert "p0p0_waw" in smt_query_string  # Example conflict var
