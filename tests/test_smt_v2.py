import io
import textwrap
from typing import Callable

from pysmt.shortcuts import (
    Symbol,
    INT,
    Int,
)
from pysmt.smtlib.parser import SmtLibParser
from pysmt.walkers import IdentityDagWalker

from p3g.graph import Loop
from p3g.parser import PseudocodeParser
from p3g.smt_v2 import exists_data_forall_bounds_forall_iters_chained


# Re-defining test helpers from test_smt.py for the new file.
# In a real-world scenario, these would be moved to a shared conftest.py or a test utils module.


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
        self.assertions.append(formula)
        return formula

    def walk_forall(self, formula):
        self.quantifiers.append(("forall", formula.quantifier_vars(), formula.arg(0)))
        return formula

    def walk_exists(self, formula):
        self.quantifiers.append(("exists", formula.quantifier_vars(), formula.arg(0)))
        return formula

    def walk_let(self, formula):
        self.let_bindings.append(formula)
        return formula


def pseudocode_to_inspector(
    psudocode: str,
    generator_function: Callable,
    extra_constraints=None,
) -> SmtQueryInspector:
    pseudocode = textwrap.dedent(psudocode).strip()
    print(pseudocode)
    parser = PseudocodeParser()
    root_graph = parser.parse(pseudocode)
    (loop,) = (n for n in root_graph.nodes if isinstance(n, Loop))
    smt_query = generator_function(loop, extra_constraints or [])
    return parse_smt_query_and_inspect(smt_query)


def parse_smt_query_and_inspect(smt_query_string: str):
    """
    Parses an SMT-LIB query string and returns an inspector object.
    """
    parser = SmtLibParser()
    script = parser.get_script(io.StringIO(smt_query_string))

    inspector = SmtQueryInspector()
    for cmd in script.commands:
        if cmd.name == "assert":
            inspector.walk_assert(cmd.args[0])
        elif cmd.name == "declare-fun":
            inspector.declarations.append(cmd)
        elif cmd.name == "check-sat":
            pass
        else:
            pass
    for assertion_formula in inspector.assertions:
        if assertion_formula.is_forall():
            inspector.walk_forall(assertion_formula)
        elif assertion_formula.is_exists():
            inspector.walk_exists(assertion_formula)
    return inspector


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_simple_loop(self):
        inspector = pseudocode_to_inspector(
            """
            sym N
            var i
            decl A, B
            out B
            (A[0:N], B[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=exists_data_forall_bounds_forall_iters_chained,
        )

        expected_declarations = {"DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
        }
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
        assert data_id_assertions == found_data_assertions_args

        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"N", "i"}

        assert q_body.is_implies()
        loop_bounds_formula, dependency_let_formula = q_body.args()

        assert loop_bounds_formula.is_and()
        assert set(str(a) for a in loop_bounds_formula.args()) == {
            "(0 <= i)",
            "((i + 1) <= N)",
            "(1 <= N)",
        }
        assert dependency_let_formula.is_equals()
        assert str(dependency_let_formula) == "(i = (i + 1))"

    def test_symbolic_lower_bound(self):
        inspector = pseudocode_to_inspector(
            """
            sym M, N
            var i
            decl A, B
            out B
            (A[M:N], B[M:N] => B[M:N]) loop1 | for i = M to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=exists_data_forall_bounds_forall_iters_chained,
        )

        expected_declarations = {"DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
        }
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
        assert data_id_assertions == found_data_assertions_args

        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"M", "N", "i"}

        assert q_body.is_implies()
        loop_bounds_formula, dependency_let_formula = q_body.args()

        assert loop_bounds_formula.is_and()
        assert set(str(a) for a in loop_bounds_formula.args()) == {
            "(M <= i)",
            "((i + 1) <= N)",
            "((M + 1) <= N)",
        }

        assert dependency_let_formula.is_equals()
        assert set(str(a) for a in dependency_let_formula.args()) == {"i", "(i + 1)"}


class TestNegatedQueryBuild:
    def test_negated_query_for_simple_loop(self):
        """
        Tests that the negated query builder produces a quantifier-free query
        checking for the existence of a counterexample.
        """

        def generator_func_negated(loop_node, extra_constraints):
            return exists_data_forall_bounds_forall_iters_chained(
                loop_node, extra_constraints, verbose=False, build_negated=True
            )

        inspector = pseudocode_to_inspector(
            """
            sym N
            var i
            decl A, B
            out B
            (A[0:N], B[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=generator_func_negated,
        )

        expected_declarations = {"N", "i", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        assert len(inspector.quantifiers) == 0

        main_assertion = None
        for formula in inspector.assertions:
            if formula.is_and() and len(formula.args()) >= 3:
                arg_strs = {str(a) for a in formula.args()}
                if "(0 <= i)" in arg_strs and "((i + 1) <= N)" in arg_strs:
                    main_assertion = formula
                    break

        assert main_assertion is not None, (
            "Main assertion And(Antecedent, ...) not found"
        )

        args_as_strings = {str(arg) for arg in main_assertion.args()}

        assert "(1 <= N)" in args_as_strings
        assert "(0 <= i)" in args_as_strings
        assert "((i + 1) <= N)" in args_as_strings
