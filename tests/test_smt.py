import io
import textwrap
from typing import Callable

from pysmt.shortcuts import (
    Symbol,
    INT,
    Plus,
    Int,
    GE,
    LE,
    ArrayType,
    Select,
    LT,
)
from pysmt.smtlib.parser import SmtLibParser
from pysmt.walkers import IdentityDagWalker

from p3g.p3g import GraphBuilder, Loop
from p3g.parser import PseudocodeParser
from p3g.smt import (
    generate_smt_for_prove_exists_data_forall_iter_isdep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
    generate_smt_for_prove_exists_data_forall_iter_isindep,
    generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
    generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
)


# Helper to create a simple P3G loop for testing
# Represents a program like:
# for i in range(0, N):
#   B[i] = A[i]
def build_simple_loop_graph():
    pseudocode = textwrap.dedent("""
    decl A, B
    out B
    (A[0:N], B[0:N] => B[0:N]) loop1 | for i = 0 to N:
      (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
    """).strip()
    parser = PseudocodeParser()
    return parser.parse(pseudocode)


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

    # 1. DEFINE top-level data handles. 'A' is read-only, 'B' and 'C' are written.
    A_root = builder.add_read_data("A")
    B_root_in, B_root_out = builder.add_write_data("B")
    C_root_in, C_root_out = builder.add_write_data("C")

    with builder.add_loop(
        "loop1",
        "i",
        Int(0),
        N,
        reads=[
            (A_root, i),
            (A_root, Plus(i, Int(1))),  # A is read at two different indices
            (B_root_in, i),  # Read B's initial value
            (C_root_in, i),  # Read C's initial value
        ],
        writes=[(B_root_out, i), (C_root_out, i)],  # Write B and C's final values
    ) as loop:
        # 3. DEFINE local handles for use *inside* the loop.
        A_local = builder.add_read_data("A")
        B_local_in, B_local_out = builder.add_write_data("B")
        C_local_in, C_local_out = builder.add_write_data("C")

        # 4. UPDATE branch signature to declare data used within its paths.
        with builder.add_branch(
            "branch1",
            reads=[
                (A_local, i),
                (A_local, Plus(i, Int(1))),
                (B_local_in, i),
                (C_local_in, i),
            ],
            writes=[(B_local_out, i), (C_local_out, i)],
        ) as branch:
            with branch.add_path(GE(x, Int(0))):
                # 5. UPDATE compute call to use local handles.
                builder.add_compute(
                    "comp_true",
                    reads=[(A_local, i), (B_local_in, i)],
                    writes=[(B_local_out, i)],
                )
            with branch.add_path(LE(x, Int(0))):
                # 6. UPDATE compute call to use local handles.
                builder.add_compute(
                    "comp_false",
                    reads=[(A_local, Plus(i, Int(1))), (C_local_in, i)],
                    writes=[(C_local_out, i)],
                )
    return (
        builder.root_graph,
        loop,
        i,
        N,
        x,
        A_root,
        (B_root_in, B_root_out),
        (C_root_in, C_root_out),
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
        inspector = pseudocode_to_inspector(
            """
            decl A, B
            out B
            (A[0:N], B[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=generate_smt_for_prove_exists_data_forall_iter_isdep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"N", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
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
        assert data_id_assertions == found_data_assertions_args

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"i"}

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        assert q_body.is_implies()  # (=> A B)
        loop_bounds_formula, dependency_let_formula = q_body.args()

        # Check loop bounds
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
            decl A, B
            out B
            (A[0:N], B[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=generate_smt_for_prove_exists_data_forall_iter_isdep,
            extra_constraints=[GE(Symbol("N", INT), Int(10))],
        )

        assert set(str(a) for a in inspector.assertions).issuperset({"(10 <= N)"})

    def test_with_array_data(self):
        inspector = pseudocode_to_inspector(
            """
            decl A
            out A
            (A[0:N] => A[0:N]) loop1 | for i = 0 to N:
              (A[i] => A[i]) comp1 | op(A[i] = 0)
            """,
            generator_function=generate_smt_for_prove_exists_data_forall_iter_isdep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"N", "DATA!A"}
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
        assert data_id_assertions == found_data_assertions_args

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"i"}

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        assert q_body.is_implies()  # (=> A B)
        loop_bounds_formula, dependency_let_formula = q_body.args()

        # Check loop bounds
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

        # Check for declarations
        expected_declarations_names = {"N", "DATA!A"}
        declared_symbols_names = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols_names.issuperset(expected_declarations_names)


class TestProveExistsDataForallLoopBoundsIterIsdep:
    def test_simple_loop(self):
        inspector = pseudocode_to_inspector(
            """
            decl A, B
            out B
            (A[0:N], B[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"N", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
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
        assert data_id_assertions == found_data_assertions_args

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"N", "i"}

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        assert q_body.is_implies()  # (=> A B)
        loop_bounds_formula, dependency_let_formula = q_body.args()

        # Check loop bounds
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

    def test_symbolic_lower_bound(self):
        inspector = pseudocode_to_inspector(
            """
            decl A, B
            out B
            (A[M:N], B[M:N] => B[M:N]) loop1 | for i = M to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"M", "N", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
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
        assert data_id_assertions == found_data_assertions_args

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"M", "N", "i"}

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        assert q_body.is_implies()  # (=> A B)
        loop_bounds_formula, dependency_let_formula = q_body.args()

        # Check loop bounds
        assert loop_bounds_formula.is_and()
        assert set(str(a) for a in loop_bounds_formula.args()) == {
            "(M <= i)",
            "((i + 1) <= N)",
            "((M + 1) <= N)",
        }

        assert dependency_let_formula.is_or()
        assert set(str(a) for a in dependency_let_formula.args()) == {
            "((DATA!B = DATA!B) & (i = (i + 1)))"
        }


class TestProveExistsDataForallIterIsindep:
    def test_simple_loop(self):
        inspector = pseudocode_to_inspector(
            """
            decl A, B
            out B
            (A[0:N], B[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=generate_smt_for_prove_exists_data_forall_iter_isindep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"N", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
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
        assert data_id_assertions == found_data_assertions_args

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"i", "i_j"}

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        assert q_body.is_implies()  # (=> A B)
        loop_bounds_formula, dependency_let_formula = q_body.args()

        # Check loop bounds
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
            decl A, B
            out B
            (A[0:N], B[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"N", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
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
        assert data_id_assertions == found_data_assertions_args

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"N", "i", "i_j"}

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        assert q_body.is_implies()  # (=> A B)
        loop_bounds_formula, dependency_let_formula = q_body.args()

        # Check loop bounds
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
            decl A, B
            out B
            (A[M:N], B[M:N] => B[M:N]) loop1 | for i = M to N:
              (A[i], B[i] => B[i]) comp1 | op(B[i] = A[i])
            """,
            generator_function=generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"M", "N", "DATA!A", "DATA!B"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
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
        assert data_id_assertions == found_data_assertions_args

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"M", "N", "i", "i_j"}

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        assert q_body.is_implies()  # (=> A B)
        loop_bounds_formula, dependency_let_formula = q_body.args()

        # Check loop bounds
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
            decl A, B, IDX
            out B
            (A[0:N], B[0:N], IDX[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[IDX[i]], B[i], IDX[i] => B[i]) comp1 | op(B[i] = A[IDX[i]])
            """,
            generator_function=generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"N", "DATA!A", "DATA!B", "DATA!IDX"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
            (Symbol("DATA!IDX", INT), Int(10003)),
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
        assert data_id_assertions == found_data_assertions_args

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"A_val", "IDX_val", "B_val"}
        assert q_body.is_forall()  # (forall ...)
        assert set(str(a) for a in q_body.quantifier_vars()) == {"i", "i_j", "N"}

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        assert q_body.arg(0).is_implies()  # (=> A B)
        loop_bounds_formula, dependency_let_formula = q_body.arg(0).args()

        # Check loop bounds
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
            decl A, B, IDX
            out B
            (A[M:N], B[M:N], IDX[M:N] => B[M:N]) loop1 | for i = M to N:
              (A[IDX[i]], B[i], IDX[i] => B[i]) comp1 | op(B[i] = A[IDX[i]])
            """,
            generator_function=generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"N", "DATA!A", "DATA!B", "DATA!IDX"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
            (Symbol("DATA!IDX", INT), Int(10003)),
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
        assert data_id_assertions == found_data_assertions_args

        # Check for quantifiers
        # We expect a single forall quantifier for the iteration variable 'i'
        assert len(inspector.quantifiers) == 1
        quantifier_type, q_vars, q_body = inspector.quantifiers[0]
        assert quantifier_type == "forall"
        assert set(str(a) for a in q_vars) == {"A_val", "IDX_val", "B_val"}
        assert q_body.is_forall()  # (forall ...)
        assert set(str(a) for a in q_body.quantifier_vars()) == {"i", "i_j", "N", "M"}

        # Check the body of the quantified formula (main assertion)
        # It should contain the loop bounds and the dependency logic
        # The structure is (=> loop_bounds (let (...) (or ...)))
        assert q_body.arg(0).is_implies()  # (=> A B)
        loop_bounds_formula, dependency_let_formula = q_body.arg(0).args()

        # Check loop bounds
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
            decl A, B, IDX
            out B
            (A[0:N], B[0:N], IDX[0:N] => B[0:N]) loop1 | for i = 0 to N:
              (A[IDX[i]], B[i], IDX[i] => B[i]) comp1 | op(B[i] = A[IDX[i]])
            """,
            generator_function=generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"N", "DATA!A", "DATA!B", "DATA!IDX"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
            (Symbol("DATA!IDX", INT), Int(10003)),
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
        assert data_id_assertions == found_data_assertions_args

        # Loop bound check
        assert set(str(a) for a in inspector.assertions).issuperset(
            {
                "((0 + 1) <= N)",
                "((0 <= i_j) & (i_j < i) & (0 <= i) & (i <= N))",
            }
        )

        # Check for quantifiers
        # We do not expect any quantifier.
        assert len(inspector.quantifiers) == 0
        q_body = inspector.assertions[-1]  # Last assert in our query
        assert q_body.is_or()
        assert set(str(a) for a in q_body.args()) == {"((DATA!B = DATA!B) & (i_j = i))"}

    def test_symbolic_lower_bound_find_dependency(self):
        inspector = pseudocode_to_inspector(
            """
            decl A, B, IDX
            out B
            (A[M:N], B[M:N], IDX[M:N] => B[M:N]) loop1 | for i = M to N:
              (A[IDX[i]], B[i], IDX[i] => B[i]) comp1 | op(B[i] = A[IDX[i]])
            """,
            generator_function=generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep,
        )

        # Check for declarations
        # We expect N, DATA!A, DATA!B, and i to be declared as Int
        expected_declarations = {"N", "DATA!A", "DATA!B", "DATA!IDX"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        # Check for data definitions (these are still global assertions)
        # We expect assertions like (= DATA!A 10001)
        data_id_assertions = {
            (Symbol("DATA!A", INT), Int(10002)),
            (Symbol("DATA!B", INT), Int(10001)),
            (Symbol("DATA!IDX", INT), Int(10003)),
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
        assert data_id_assertions == found_data_assertions_args

        # Loop bound check
        assert set(str(a) for a in inspector.assertions).issuperset(
            {
                "((M + 1) <= N)",
                "((M <= i_j) & (i_j < i) & (M <= i) & (i <= N))",
            }
        )

        # Check for quantifiers
        # We do not expect any quantifier.
        assert len(inspector.quantifiers) == 0
        q_body = inspector.assertions[-1]  # Last assert in our query
        assert q_body.is_or()
        assert set(str(a) for a in q_body.args()) == {"((DATA!B = DATA!B) & (i_j = i))"}
