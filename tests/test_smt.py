import io
import textwrap
from typing import Callable

from pysmt.shortcuts import (
    Symbol,
    INT,
    Int,
    GE,
)
from pysmt.smtlib.parser import SmtLibParser
from pysmt.walkers import IdentityDagWalker

from p3g.graph import Loop
from p3g.parser import PseudocodeParser
from p3g.smt import (
    exists_data_exists_bounds_forall_iter_isdep,
    exists_data_exists_bounds_forall_iter_isindep,
    exists_data_forall_bounds_forall_iter_isindep,
    forall_data_forall_bounds_forall_iter_isindep,
    exists_data_exists_bounds_exists_iter_isdep,
)


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


class TestProveExistsDataForallIterIsdep:
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
            generator_function=exists_data_exists_bounds_forall_iter_isdep,
        )

        expected_declarations = {"N", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
            (Symbol("DATA!B", INT), Int(10002)),
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
        assert set(str(a) for a in q_vars) == {"i"}

        assert q_body.is_implies()
        loop_bounds_formula, dependency_let_formula = q_body.args()

        assert loop_bounds_formula.is_and()
        assert set(str(a) for a in loop_bounds_formula.args()) == {
            "(0 <= i)",
            "((i + 1) <= N)",
            "((0 + 1) <= N)",
        }

        assert dependency_let_formula.is_or()
        assert set(str(a) for a in dependency_let_formula.args()) == {
            "((DATA!B = DATA!B) & (i = (i + 1)))"
        }

    def test_with_extra_assertions(self):
        inspector = pseudocode_to_inspector(
            """
            sym N
            var i
            decl A, B
            out B
            (A[0:N], B[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=exists_data_exists_bounds_forall_iter_isdep,
            extra_constraints=[GE(Symbol("N", INT), Int(10))],
        )

        assert set(str(a) for a in inspector.assertions).issuperset({"(10 <= N)"})

    def test_with_array_data(self):
        inspector = pseudocode_to_inspector(
            """
            sym N
            var i
            decl A
            out A
            (A[0:N] => A[0:N]) loop1 | for i = 0 to N:
              (A[i] => A[i]) comp1 | op(A[i] = 0)
            """,
            generator_function=exists_data_exists_bounds_forall_iter_isdep,
        )

        expected_declarations = {"N", "DATA!A"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
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
        assert set(str(a) for a in q_vars) == {"i"}

        assert q_body.is_implies()
        loop_bounds_formula, dependency_let_formula = q_body.args()

        assert loop_bounds_formula.is_and()
        assert set(str(a) for a in loop_bounds_formula.args()) == {
            "(0 <= i)",
            "((i + 1) <= N)",
            "((0 + 1) <= N)",
        }

        assert dependency_let_formula.is_or()
        assert set(str(a) for a in dependency_let_formula.args()) == {
            "((DATA!A = DATA!A) & (i = (i + 1)))"
        }

        expected_declarations_names = {"N", "DATA!A"}
        declared_symbols_names = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols_names.issuperset(expected_declarations_names)


class TestProveExistsDataForallIterIsindep:
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
            generator_function=exists_data_exists_bounds_forall_iter_isindep,
        )

        expected_declarations = {"N", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
            (Symbol("DATA!B", INT), Int(10002)),
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
        assert set(str(a) for a in q_vars) == {"i", "i_j"}

        assert q_body.is_implies()
        loop_bounds_formula, dependency_let_formula = q_body.args()

        assert loop_bounds_formula.is_and()
        assert set(str(a) for a in loop_bounds_formula.args()) == {
            "(0 <= i)",
            "(0 <= i_j)",
            "(i_j < i)",
            "(i <= N)",
        }

        assert dependency_let_formula.is_not()
        assert dependency_let_formula.arg(0).is_or()
        assert set(str(a) for a in dependency_let_formula.arg(0).args()) == {
            "((DATA!B = DATA!B) & (i_j = i))"
        }


class TestProveExistsDataForallLoopBoundsIterIsindep:
    def test_simple_loop_independence_forall_bounds(self):
        inspector = pseudocode_to_inspector(
            """
            sym N
            var i
            decl A, B
            out B
            (A[0:N], B[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=exists_data_forall_bounds_forall_iter_isindep,
        )

        expected_declarations = {"N", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
            (Symbol("DATA!B", INT), Int(10002)),
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
        assert set(str(a) for a in q_vars) == {"N", "i", "i_j"}

        assert q_body.is_implies()
        loop_bounds_formula, dependency_let_formula = q_body.args()

        assert loop_bounds_formula.is_and()
        assert set(str(a) for a in loop_bounds_formula.args()) == {
            "(0 <= i)",
            "(0 <= i_j)",
            "(i_j < i)",
            "(i <= N)",
        }

        assert dependency_let_formula.is_not()
        assert dependency_let_formula.arg(0).is_or()
        assert set(str(a) for a in dependency_let_formula.arg(0).args()) == {
            "((DATA!B = DATA!B) & (i_j = i))"
        }

    def test_symbolic_lower_bound_forall_bounds(self):
        inspector = pseudocode_to_inspector(
            """
            sym M, N
            var i
            decl A, B
            out B
            (A[M:N], B[M:N] => B[M:N]) loop1 | for i = M to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=exists_data_forall_bounds_forall_iter_isindep,
        )

        expected_declarations = {"M", "N", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
            (Symbol("DATA!B", INT), Int(10002)),
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
        assert set(str(a) for a in q_vars) == {"M", "N", "i", "i_j"}

        assert q_body.is_implies()
        loop_bounds_formula, dependency_let_formula = q_body.args()

        assert loop_bounds_formula.is_and()
        assert set(str(a) for a in loop_bounds_formula.args()) == {
            "(M <= i)",
            "(M <= i_j)",
            "(i_j < i)",
            "(i <= N)",
        }

        assert dependency_let_formula.is_not()
        assert dependency_let_formula.arg(0).is_or()
        assert set(str(a) for a in dependency_let_formula.arg(0).args()) == {
            "((DATA!B = DATA!B) & (i_j = i))"
        }


class TestProveForallDataForallLoopBoundsIterIsindep:
    def test_simple_loop_independence_forall_data_forall_bounds(self):
        inspector = pseudocode_to_inspector(
            """
            sym N
            var i
            decl A, B, IDX
            out B
            (A[0:N], B[0:N], IDX[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[IDX[i]], B[i], IDX[i] => B[i]) comp1 | op(B[i] = A[IDX[i]])
            """,
            generator_function=forall_data_forall_bounds_forall_iter_isindep,
        )

        expected_declarations = {"N", "DATA!A", "DATA!B", "DATA!IDX"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
            (Symbol("DATA!B", INT), Int(10002)),
            (Symbol("DATA!IDX", INT), Int(10003)),
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
        assert set(str(a) for a in q_vars) == {"A_val", "IDX_val", "B_val"}
        assert q_body.is_forall()
        assert set(str(a) for a in q_body.quantifier_vars()) == {"i", "i_j", "N"}

        assert q_body.arg(0).is_implies()
        loop_bounds_formula, dependency_let_formula = q_body.arg(0).args()

        assert loop_bounds_formula.is_and()
        assert set(str(a) for a in loop_bounds_formula.args()) == {
            "(0 <= i)",
            "(0 <= i_j)",
            "(i_j < i)",
            "(i <= N)",
        }

        assert dependency_let_formula.is_not()
        assert dependency_let_formula.arg(0).is_or()
        assert set(str(a) for a in dependency_let_formula.arg(0).args()) == {
            "((DATA!B = DATA!B) & (i_j = i))"
        }

    def test_symbolic_lower_bound_forall_data_forall_bounds(self):
        inspector = pseudocode_to_inspector(
            """
            sym M, N
            var i
            decl A, B, IDX
            out B
            (A[M:N], B[M:N], IDX[M:N] => B[M:N]) loop1 | for i = M to N:
              (A[IDX[i]], B[i], IDX[i] => B[i]) comp1 | op(B[i] = A[IDX[i]])
            """,
            generator_function=forall_data_forall_bounds_forall_iter_isindep,
        )

        expected_declarations = {"N", "DATA!A", "DATA!B", "DATA!IDX"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
            (Symbol("DATA!B", INT), Int(10002)),
            (Symbol("DATA!IDX", INT), Int(10003)),
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
        assert set(str(a) for a in q_vars) == {"A_val", "IDX_val", "B_val"}
        assert q_body.is_forall()
        assert set(str(a) for a in q_body.quantifier_vars()) == {"i", "i_j", "N", "M"}

        assert q_body.arg(0).is_implies()
        loop_bounds_formula, dependency_let_formula = q_body.arg(0).args()

        assert loop_bounds_formula.is_and()
        assert set(str(a) for a in loop_bounds_formula.args()) == {
            "(M <= i)",
            "(M <= i_j)",
            "(i_j < i)",
            "(i <= N)",
        }

        assert dependency_let_formula.is_not()
        assert dependency_let_formula.arg(0).is_or()
        assert set(str(a) for a in dependency_let_formula.arg(0).args()) == {
            "((DATA!B = DATA!B) & (i_j = i))"
        }


class TestProveExistsDataExistsLoopBoundsExistsIterIsdep:
    def test_simple_loop_find_dependency(self):
        inspector = pseudocode_to_inspector(
            """
            sym N
            var i
            decl A, B, IDX
            out B
            (A[0:N], B[0:N], IDX[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[IDX[i]], B[i], IDX[i] => B[i]) comp1 | op(B[i] = A[IDX[i]])
            """,
            generator_function=exists_data_exists_bounds_exists_iter_isdep,
        )

        expected_declarations = {"N", "DATA!A", "DATA!B", "DATA!IDX"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
            (Symbol("DATA!B", INT), Int(10002)),
            (Symbol("DATA!IDX", INT), Int(10003)),
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

        assert set(str(a) for a in inspector.assertions).issuperset(
            {
                "((0 + 1) <= N)",
                "((0 <= i_j) & (i_j < i) & (0 <= i) & (i <= N))",
            }
        )

        assert len(inspector.quantifiers) == 0
        q_body = inspector.assertions[-1]
        assert q_body.is_or()
        assert set(str(a) for a in q_body.args()) == {"((DATA!B = DATA!B) & (i_j = i))"}

    def test_symbolic_lower_bound_find_dependency(self):
        inspector = pseudocode_to_inspector(
            """
            sym M, N
            var i
            decl A, B, IDX
            out B
            (A[M:N], B[M:N], IDX[M:N] => B[M:N]) loop1 | for i = M to N:
              (A[IDX[i]], B[i], IDX[i] => B[i]) comp1 | op(B[i] = A[IDX[i]])
            """,
            generator_function=exists_data_exists_bounds_exists_iter_isdep,
        )

        expected_declarations = {"N", "DATA!A", "DATA!B", "DATA!IDX"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10001)),
            (Symbol("DATA!B", INT), Int(10002)),
            (Symbol("DATA!IDX", INT), Int(10003)),
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

        assert set(str(a) for a in inspector.assertions).issuperset(
            {
                "((M + 1) <= N)",
                "((M <= i_j) & (i_j < i) & (M <= i) & (i <= N))",
            }
        )

        assert len(inspector.quantifiers) == 0
        q_body = inspector.assertions[-1]
        assert q_body.is_or()
        assert set(str(a) for a in q_body.args()) == {"((DATA!B = DATA!B) & (i_j = i))"}
