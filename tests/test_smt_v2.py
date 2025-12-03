import io
import textwrap
from typing import Callable

from pysmt.shortcuts import (
    Symbol,
    INT,
    Int,
    Equals,
    GE,
)
from pysmt.smtlib.parser import SmtLibParser
from pysmt.walkers import IdentityDagWalker

from p3g.graph import Loop
from p3g.parser import PseudocodeParser
from p3g.smt_v2 import (
    exists_data_forall_bounds_forall_iters_chained,
    _build_analysis_context,
)


# Test helpers shared across different test classes in this module.
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
    parser = PseudocodeParser()
    root_graph = parser.parse(pseudocode)
    # The generator_function expects a Loop node. We assume there's exactly one top-level loop.
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
        # Recursively walk the assertion to find any nested quantifiers
        queue = [assertion_formula]
        while queue:
            formula = queue.pop(0)
            if formula.is_forall():
                inspector.walk_forall(formula)
            elif formula.is_exists():
                inspector.walk_exists(formula)
            elif formula.is_and() or formula.is_or():
                queue.extend(formula.args())
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

        expected_declarations = set()
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

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
            "(! (i = (i + 1)))",
        }
        assert dependency_let_formula.is_false()

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

        expected_declarations = set()
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

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
            "(! (i = (i + 1)))",
        }

        assert dependency_let_formula.is_false()


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

        expected_declarations = {"N", "i"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)

        assert len(inspector.quantifiers) == 0

        assert len(inspector.assertions) == 1
        main_assertion_formula = inspector.assertions[0]
        assert main_assertion_formula.is_and()

        # The top-level AND has two arguments: the bounds-AND and the not-equal clause
        assert len(main_assertion_formula.args()) == 2

        bounds_and_formula = None
        not_equal_formula = None

        for arg in main_assertion_formula.args():
            if arg.is_and():
                bounds_and_formula = arg
            elif str(arg) == "(! (i = (i + 1)))":
                not_equal_formula = arg

        assert bounds_and_formula is not None
        assert not_equal_formula is not None

        bounds_arg_strs = {str(a) for a in bounds_and_formula.args()}

        assert "(0 <= i)" in bounds_arg_strs
        assert "((i + 1) <= N)" in bounds_arg_strs
        assert "(1 <= N)" in bounds_arg_strs

    def test_negated_query_with_indirect_access(self):
        """
        Tests that the negated query builder introduces a ForAll quantifier
        when data-dependent (indirect) access is present.
        """

        def generator_func_negated(loop_node, extra_constraints):
            return exists_data_forall_bounds_forall_iters_chained(
                loop_node, extra_constraints, verbose=True, build_negated=True
            )

        inspector = pseudocode_to_inspector(
            """
            sym N
            var i
            decl A, B
            out A
            (A[0:N], B[0:N] => A[0:N]) loop1 | for i = 0 to N:
              (A[B[i]], B[i] => A[B[i]]) comp1 | op(A[B[i]] = B[i])
            """,
            generator_function=generator_func_negated,
        )

        expected_declarations = {"N", "i"}
        declared_symbols = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert declared_symbols.issuperset(expected_declarations)
        # B_val should NOT be in declared symbols (global), because it should be quantified
        assert not any(s.endswith("_val") for s in declared_symbols)

        assert len(inspector.quantifiers) == 1
        q_type, q_vars, q_body = inspector.quantifiers[0]
        assert q_type == "forall"

        # Check that we are quantifying over B_val (represented as an array or function)
        # In P3G/PySMT, B_val is usually a function Int -> Int or Array.
        q_var_names = {str(v) for v in q_vars}
        assert any("B_val" in v for v in q_var_names)

    def test_nested_sibling_loops_assertions(self):
        """
        Tests that assertions from nested sibling loops are not leaked into the
        global scope when analyzing the outer loop.
        """

        def generator_func(loop_node, extra_constraints):
            return exists_data_forall_bounds_forall_iters_chained(
                loop_node, extra_constraints, verbose=False, build_negated=False
            )

        inspector = pseudocode_to_inspector(
            """
            sym N
            var i, j, k
            decl A
            out A
            (A[0:N] => A[0:N]) loop_outer | for i = 0 to N:
                (A[i] => A[i]) loop_j | for j = 0 to i:
                     (A[j] => A[j]) op1 | op(A[j] = A[j] + 1)
                (A[i] => A[i]) loop_k | for k = i to N:
                     (A[k] => A[k]) op2 | op(A[k] = A[k] * 2)
            """,
            generator_function=generator_func,
        )

        declared_names = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }

        assert "j" not in declared_names, "Inner loop var 'j' leaked to global scope"
        assert "k" not in declared_names, "Inner loop var 'k' leaked to global scope"

        for assertion in inspector.assertions:
            if assertion.is_forall():
                continue

            vars_in_assertion = {
                v.symbol_name() for v in assertion.get_free_variables()
            }
            assert "j" not in vars_in_assertion
            assert "k" not in vars_in_assertion

    def test_deeply_nested_assertions(self):
        """
        Tests that assertions from deeply nested loops (Inner2 inside Inner1 inside Outer)
        are not leaked into the global scope when analyzing the Outer loop.
        Mimics the Nussinov structure.
        """

        def generator_func(loop_node, extra_constraints):
            return exists_data_forall_bounds_forall_iters_chained(
                loop_node, extra_constraints, verbose=False, build_negated=False
            )

        inspector = pseudocode_to_inspector(
            """
            sym N
            var i, j, k
            decl A
            out A
            (A[0:N] => A[0:N]) loop_outer | for i = 0 to N:
                (A[i] => A[i]) loop_j | for j = 0 to i:
                     (A[j] => A[j]) op1 | op(A[j] = A[j] + 1)
                     (A[j] => A[j]) loop_k | for k = j to i:
                          (A[k] => A[k]) op2 | op(A[k] = A[k] * 2)
            """,
            generator_function=generator_func,
        )

        declared_names = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }

        assert "j" not in declared_names, "Inner loop var 'j' leaked to global scope"
        assert "k" not in declared_names, (
            "Deeply nested loop var 'k' leaked to global scope"
        )

        for assertion in inspector.assertions:
            if assertion.is_forall():
                continue

            vars_in_assertion = {
                v.symbol_name() for v in assertion.get_free_variables()
            }
            assert "j" not in vars_in_assertion
            assert "k" not in vars_in_assertion

    def test_outer_loop_bounds_in_antecedent(self):
        """
        Tests that bounds for the outer (universal) loop ARE added to the
        global antecedent to constrain the counterexample search space.
        """

        def generator_func(loop_node, extra_constraints):
            return exists_data_forall_bounds_forall_iters_chained(
                loop_node, extra_constraints, verbose=False, build_negated=True
            )

        inspector = pseudocode_to_inspector(
            """
            sym N
            var i
            decl A
            out A
            (A[0:N] => A[0:N]) loop_outer | for i = 0 to N:
                 (A[i] => A[i]) op1 | op(A[i] = A[i] + 1)
            """,
            generator_function=generator_func,
        )

        assert len(inspector.assertions) == 1
        main_assertion = inspector.assertions[0]
        assert main_assertion.is_and()

        # The main assertion should be And(Antecedent, Not(Consequent)).
        # The Antecedent might be a nested And.

        found_bounds = False
        for arg in main_assertion.args():
            # We are looking for the antecedent block which should contain the bounds.
            # It might be a single And containing (0 <= i) etc.
            if arg.is_and():
                sub_args = {str(sub) for sub in arg.args()}
                if "(0 <= i)" in sub_args or "(i <= N)" in sub_args:
                    found_bounds = True
                    assert "(0 <= i)" in sub_args
                    # assert "(i <= N)" in sub_args  # Likely optimized away
                    assert "(1 <= N)" in sub_args
                    assert "((i + 1) <= N)" in sub_args
                    break

        assert found_bounds, "Outer loop bounds not found in global assertions"

        # Ensure that no inner loop variables are unexpectedly declared
        declared_names = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }
        assert "j" not in declared_names
        assert "k" not in declared_names

    def test_inner_loop_independent_bounds(self):
        """
        Tests that an inner loop with bounds dependent only on global parameters
        (like TRMM: for j = 0 to N) does not leak its variable to the global scope.
        """

        def generator_func(loop_node, extra_constraints):
            return exists_data_forall_bounds_forall_iters_chained(
                loop_node, extra_constraints, verbose=True, build_negated=True
            )

        inspector = pseudocode_to_inspector(
            """
            sym M, N
            var i, j
            decl A
            out A
            (A[0:M, 0:N] => A[0:M, 0:N]) loop_i | for i = 0 to M:
                 (A[0:M, 0:N] => A[0:M, 0:N]) loop_j | for j = 0 to N:
                      (A[i,j] => A[i,j]) comp | op(A[i,j] = A[i,j] + 1)
            """,
            generator_function=generator_func,
        )

        declared_names = {
            cmd.args[0].symbol_name()
            for cmd in inspector.declarations
            if cmd.name == "declare-fun"
        }

        # 'i' is universal (outer), so it might be declared or quantified depending on logic.
        # In 'exists_data_forall_bounds_forall_iters_chained', k (loop var) is universal.
        # 'build_negated_query' makes universals existential (free global).
        # So 'i' should be declared.
        assert "i" in declared_names
        assert "M" in declared_names
        assert "N" in declared_names

        # Check that we assert inner loop is non-empty (N >= 1)
        # This comes from _collect_nested_loop_checks adding LE(start+1, end) -> 0+1 <= N
        main_assertion = inspector.assertions[0]
        arg_strs = {str(a) for a in main_assertion.args() if not a.is_forall()}
        # Flatten args if they are nested Ands
        flat_args = set()
        queue = list(main_assertion.args())
        while queue:
            a = queue.pop(0)
            if a.is_and():
                queue.extend(a.args())
            else:
                flat_args.add(str(a))

        assert "(1 <= N)" in flat_args, "Inner loop non-empty constraint missing"

        # 'j' is inner. It should be quantified locally inside the formula.
        assert "j" not in declared_names, (
            "Inner loop variable 'j' leaked to global scope"
        )

        # Check that 'j' (or j_0) appears in a quantifier
        found_j_quantifier = False
        for q_type, q_vars, _ in inspector.quantifiers:
            if q_type == "forall":
                if any("j" in str(v) for v in q_vars):
                    found_j_quantifier = True
                    break
        assert found_j_quantifier, "Inner loop variable 'j' not found in quantifiers"


class TestAnalysisContextBuilding:
    def test_basic_context_building(self):
        pseudocode = """
            sym N, M
            var i, j
            decl A, B
            out B
            (A[0:N], B[0:N] => B[0:N]) loop_outer | for i = 0 to N:
                ! (< i N)
                (A[0:M], B[0:M] => B[0:M]) loop_inner | for j = 0 to M:
                    (A[j], B[j] => B[j]) comp1 | op(B[j] = A[j])
                (A[i] => A[i]) comp2 | op(A[i] = A[i] + 1)
        """
        parser = PseudocodeParser()
        root_graph = parser.parse(textwrap.dedent(pseudocode).strip())

        # Find the outer loop node
        outer_loop_node = None
        for node in root_graph.nodes:
            if isinstance(node, Loop) and node.name == "loop_outer":
                outer_loop_node = node
                break
        assert outer_loop_node is not None, "Outer loop node not found"

        extra_assertions = [
            GE(Symbol("N", INT), Int(1)),
            Equals(Symbol("N", INT), Int(10)),
        ]

        context = _build_analysis_context(root_graph, outer_loop_node, extra_assertions)

        # Assert all_data_nodes
        expected_data_node_names = {
            "A(0)",
            "B(0)",
            "A(1)",
            "B(1)",
            "A(2)",
            "B(2)",
            "B(3)",
        }
        data_node_names = {node.name for node in context.all_data_nodes}
        assert data_node_names.issuperset(expected_data_node_names)

        # Assert id_to_array_name and id_to_location_symbol_map
        assert {"A", "B"}.issubset(context.id_to_array_name.values())

        array_a_id = next(
            id for id, name in context.id_to_array_name.items() if name == "A"
        )
        array_b_id = next(
            id for id, name in context.id_to_array_name.items() if name == "B"
        )
        assert context.id_to_location_symbol_map[array_a_id].symbol_name() == "DATA!A"
        assert context.id_to_location_symbol_map[array_b_id].symbol_name() == "DATA!B"

        # Assert loop_bound_symbols
        expected_loop_bound_sym_names = {"N", "M"}
        loop_bound_sym_names = {s.symbol_name() for s in context.loop_bound_symbols}
        assert loop_bound_sym_names.issuperset(expected_loop_bound_sym_names)
        assert "i" not in loop_bound_sym_names  # loop vars are not loop bound symbols
        assert "j" not in loop_bound_sym_names

        # Assert universal_vars (outer loop var 'i', and global symbols N, M)
        expected_universal_var_names = {"i", "N", "M"}
        universal_var_names = {s.symbol_name() for s in context.universal_vars}
        assert universal_var_names.issuperset(expected_universal_var_names)
        assert (
            "j" not in universal_var_names
        )  # Inner loop var 'j' should not be universal here

        # Assert all_assertions
        expected_assertion_strs = {
            "(1 <= N)",  # From extra_assertions: GE(N,1) is normalized to 1 <= N
            "(N = 10)",  # From extra_assertions: Equals(N,10)
            "(i < N)",  # From loop_outer's ! (< i N)
            "((0 + 1) <= M)",  # From loop_inner non-empty check
            "((0 + 1) <= N)",  # From loop_outer non-empty check
        }
        assertion_strs = {str(a) for a in context.all_assertions}
        assert assertion_strs.issuperset(expected_assertion_strs)

        # Assert extra_assertions
        expected_extra_assertion_strs = {
            "(1 <= N)",
            "(N = 10)",
        }  # Note: PySMT converts GE to LE
        extra_assertion_strs = {str(a) for a in context.extra_assertions}
        assert extra_assertion_strs.issuperset(expected_extra_assertion_strs)

        # Assert all_compute_items
        expected_compute_node_names = {"comp1", "comp2"}
        compute_node_names = {
            item.compute_node.name for item in context.all_compute_items
        }
        assert compute_node_names.issuperset(expected_compute_node_names)
