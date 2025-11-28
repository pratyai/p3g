"""
Revised SMT query generation for P3G.

This version generates a query to prove that for a given loop, there EXISTS a
data configuration such that FORALL loop bounds and FORALL iterations, a
dependency is present. This version uses a structured SmtQueryBuilder.
"""

from __future__ import annotations

import io
import itertools
from collections import namedtuple

from pysmt.shortcuts import (
    Symbol,
    Equals,
    And,
    Or,
    Plus,
    Int,
    GE,
    LE,
    Exists,
    ForAll,
    get_free_variables,
    substitute,
    TRUE,
    FALSE,
    simplify,
    Not,
)
from pysmt.smtlib.printers import SmtPrinter
from pysmt.typing import INT
from pysmt.rewritings import NNFizer, PrenexNormalizer

from p3g.graph import Graph, Loop, Data, Compute, Branch
from p3g.subsets import (
    _create_set_intersection_formula,
    substitute_subset,
    PysmtFormula,
    _get_free_variables_recursive,
    PysmtSymbol,
)

ComputeItem = namedtuple("ComputeItem", ["path_cond", "compute_node", "loops"])


class SmtQueryBuilder:
    """A structured builder for the specific SMT query pattern needed."""

    def __init__(self):
        self._universal_vars: set[PysmtSymbol] = set()
        self._existential_vars: set[PysmtSymbol] = set()
        self._antecedent_clauses: list[PysmtFormula] = []
        self._consequent_clauses: list[PysmtFormula] = []
        self._toplevel_assertions: list[PysmtFormula] = []

        self._string_io = io.StringIO()
        self._printer = SmtPrinter(self._string_io)

    def _collect_all_free_variables(self, formula: PysmtFormula):
        """Recursively collects all free variables in a formula into _existential_vars."""
        if formula is None:
            return
        for sym in get_free_variables(formula):
            self.add_existential_var(sym)

    def _pretty_print(self, formula: PysmtFormula, indent_level: int = 0) -> str:
        """Serializes a pysmt formula with custom pretty-printing for major connectives."""
        indent = "  " * indent_level

        if formula is None:
            return f"{indent}true"

        # Special formatting for quantifiers
        if formula.is_quantifier():
            quantifier_str = "forall" if formula.is_forall() else "exists"
            quantified_vars = sorted(
                formula.quantifier_vars(), key=lambda s: s.symbol_name()
            )

            vars_str = " ".join(
                [f"({s.symbol_name()} {s.get_type()})" for s in quantified_vars]
            )
            body_str = self._pretty_print(formula.arg(0), indent_level + 1)

            return f"{indent}({quantifier_str} ({vars_str})\n{body_str}\n{indent})"

        # Special formatting for Implies
        if formula.is_implies():
            left_str = self._pretty_print(formula.arg(0), indent_level + 1)
            right_str = self._pretty_print(formula.arg(1), indent_level + 1)
            return f"{indent}(=>\n{left_str}\n{right_str}\n{indent})"

        # Special formatting for And/Or to indent arguments
        if formula.is_and() or formula.is_or():
            op_str = "and" if formula.is_and() else "or"
            args = formula.args()

            # Delegate empty or single-argument And/Or to default printer after simplification
            # or handle multiple arguments with custom indentation
            if len(args) > 1:
                args_strs = [self._pretty_print(arg, indent_level + 1) for arg in args]
                return f"{indent}({op_str}\n{'\n'.join(args_strs)}\n{indent})"

        # Default pysmt serialization for atomic formulas and other operators
        # This will also handle empty or single-argument And/Or after simplification
        self._string_io.seek(0)
        self._string_io.truncate(0)
        self._printer.printer(formula)
        return f"{indent}{self._string_io.getvalue()}"

    def add_universal_var(self, var: PysmtSymbol):
        self._universal_vars.add(var)

    def add_existential_var(self, var: PysmtSymbol):
        if var not in self._universal_vars:
            self._existential_vars.add(var)

    def add_antecedent_clause(self, clause: PysmtFormula):
        if clause and not clause.is_true():
            self._antecedent_clauses.append(clause)

    def add_consequent_clause(self, clause: PysmtFormula):
        if clause and not clause.is_false():
            self._consequent_clauses.append(clause)

    def add_toplevel_assertion(self, clause: PysmtFormula):
        """Adds an assertion that will appear at the top level, outside the main forall."""
        if clause and not clause.is_true():
            self._toplevel_assertions.append(clause)

    def build_query(self) -> str:
        """Assembles and returns the final SMT-LIB query string with pretty-printing."""
        # Step 1: Build the main formula object
        antecedent = (
            And(self._antecedent_clauses) if self._antecedent_clauses else TRUE()
        )
        consequent = (
            Or(self._consequent_clauses) if self._consequent_clauses else FALSE()
        )

        sorted_universals = sorted(
            list(self._universal_vars), key=lambda s: s.symbol_name()
        )

        main_formula = ForAll(sorted_universals, Or(Not(antecedent), consequent))
        main_formula = simplify(main_formula)
        # main_formula = NNFizer().convert(main_formula)
        # main_formula = simplify(main_formula)
        # main_formula = PrenexNormalizer().normalize(main_formula)
        # main_formula = simplify(main_formula)

        # Step 2: Collect all free variables for the declaration header
        # To avoid statefulness issues, we use a local set for this build.
        local_existential_vars = self._existential_vars.copy()

        def collect_free_vars_local(formula: PysmtFormula):
            if formula is None:
                return
            for sym in get_free_variables(formula):
                if sym not in self._universal_vars:
                    local_existential_vars.add(sym)

        collect_free_vars_local(main_formula)
        simplified_toplevel_assertions = []
        for assertion in self._toplevel_assertions:
            simplified_assertion = simplify(assertion)
            collect_free_vars_local(simplified_assertion)
            simplified_toplevel_assertions.append(simplified_assertion)

        # Step 3: Pretty-print all assertions
        toplevel_assertion_strs = [
            f"(assert {self._pretty_print(a, 0)})"
            for a in simplified_toplevel_assertions
        ]
        main_assertion_str = f"(assert {self._pretty_print(main_formula, 0)})"

        # Step 4: Build declarations for all collected free (existential) variables
        final_existentials = local_existential_vars - self._universal_vars

        def get_decl_str(s: PysmtSymbol) -> str:
            t = s.get_type()
            if t.is_int_type():
                return f"(declare-fun {s.symbol_name()} () Int)"
            if t.is_array_type():
                return f"(declare-fun {s.symbol_name()} () (Array {t.index_type} {t.elem_type}))"
            return f"(declare-fun {s.symbol_name()} () {t})"

        header = sorted([get_decl_str(d) for d in final_existentials], key=str)

        all_assertions_parts = []
        if toplevel_assertion_strs:
            all_assertions_parts.append("\n".join(toplevel_assertion_strs))
            all_assertions_parts.append("")  # Add the empty line here
        all_assertions_parts.append(main_assertion_str)

        all_assertions = "\n".join(all_assertions_parts)

        return "\n".join(header) + f"\n\n{all_assertions}\n\n(check-sat)"

    def build_negated_query(self) -> str:
        """
        Assembles a quantifier-free query to check for the existence of a counterexample
        to the main universally-quantified property.

        It constructs `NOT(FORALL ...)` which simplifies to `EXISTS (NOT (...))`.
        This effectively asks the solver: "Does there exist a set of indices/parameters
        where the loop bounds are valid (Antecedent is true) BUT no dependency exists
        (Consequent is false)?"

        The result is a quantifier-free formula (after skolemization/instantiation)
        that is satisfiable if and only if the original property is invalid.
        """
        antecedent = (
            And(self._antecedent_clauses) if self._antecedent_clauses else TRUE()
        )
        consequent = (
            Or(self._consequent_clauses) if self._consequent_clauses else FALSE()
        )

        sorted_universals = sorted(
            list(self._universal_vars), key=lambda s: s.symbol_name()
        )

        main_formula = Not(ForAll(sorted_universals, Or(Not(antecedent), consequent)))
        main_formula = simplify(main_formula)
        main_formula = NNFizer().convert(main_formula)
        self._universal_vars.clear()
        assert main_formula.is_exists()
        (main_formula,) = main_formula.args()

        # Step 2: Collect all free variables for the declaration header
        # To avoid statefulness issues, we use a local set for this build.
        local_existential_vars = self._existential_vars.copy()

        def collect_free_vars_local(formula: PysmtFormula):
            if formula is None:
                return
            for sym in get_free_variables(formula):
                if sym not in self._universal_vars:
                    local_existential_vars.add(sym)

        collect_free_vars_local(main_formula)
        simplified_toplevel_assertions = []
        for assertion in self._toplevel_assertions:
            simplified_assertion = simplify(assertion)
            collect_free_vars_local(simplified_assertion)
            simplified_toplevel_assertions.append(simplified_assertion)

        # Step 3: Pretty-print all assertions
        toplevel_assertion_strs = [
            f"(assert {self._pretty_print(a, 0)})"
            for a in simplified_toplevel_assertions
        ]
        main_assertion_str = f"(assert {self._pretty_print(main_formula, 0)})"

        # Step 4: Build declarations for all collected free (existential) variables
        final_existentials = local_existential_vars - self._universal_vars

        def get_decl_str(s: PysmtSymbol) -> str:
            t = s.get_type()
            if t.is_int_type():
                return f"(declare-fun {s.symbol_name()} () Int)"
            if t.is_array_type():
                return f"(declare-fun {s.symbol_name()} () (Array {t.index_type} {t.elem_type}))"
            return f"(declare-fun {s.symbol_name()} () {t})"

        header = sorted([get_decl_str(d) for d in final_existentials], key=str)

        all_assertions_parts = []
        if toplevel_assertion_strs:
            all_assertions_parts.append("\n".join(toplevel_assertion_strs))
            all_assertions_parts.append("")  # Add the empty line here
        all_assertions_parts.append(main_assertion_str)

        all_assertions = "\n".join(all_assertions_parts)

        return "\n".join(header) + f"\n\n{all_assertions}\n\n(check-sat)"


def _flatten_graph_to_compute_items(
    graph: Graph, path_cond: PysmtFormula = TRUE(), loops: list[Loop] = None
) -> list[ComputeItem]:
    """Flattens the graph into a list of compute nodes with their context."""
    if loops is None:
        loops = []
    items = []
    for node in graph.nodes:
        if isinstance(node, Compute):
            items.append(ComputeItem(path_cond, node, loops))
        elif isinstance(node, Branch):
            for pred, nested_g in node.branches:
                new_cond = And(path_cond, pred)
                items.extend(_flatten_graph_to_compute_items(nested_g, new_cond, loops))
        elif isinstance(node, Loop):
            new_loops = loops + [node]
            items.extend(
                _flatten_graph_to_compute_items(node.nested_graph, path_cond, new_loops)
            )
    return items


def _find_conflict_elements(
    loop_body_graph: Graph,
    k: PysmtSymbol,
    id_to_val_symbol_map: dict[int, PysmtSymbol],
) -> list[
    tuple[set[PysmtSymbol], list[PysmtFormula], list[PysmtFormula], list[PysmtFormula]]
]:
    """
    Finds all dependency clauses and adds them to the builder's consequent.
    """
    conflict_elements = []
    items = _flatten_graph_to_compute_items(loop_body_graph)

    # For each pair of compute items, generate a dependency clause
    for (pc1, comp1, loops1), (pc2, comp2, loops2) in itertools.product(
        items, repeat=2
    ):
        existential_vars = set()
        subst = [{}, {}]

        # Create existential vars for inner loops (at outer iter k and k+1)
        bounds = []
        for offset, loops in [(0, loops1), (1, loops2)]:
            for loop in loops:
                var = loop.loop_var
                v = Symbol(f"{var.symbol_name()}_{offset}", INT)
                existential_vars.add(v)
                subst[offset][var] = v
                bounds.append(
                    And(
                        GE(v, substitute(loop.start, {k: k + Int(offset)})),
                        LE(v, substitute(loop.end, {k: k + Int(offset)})),
                    )
                )

        # Path conditions with substitutions
        path_conds = [
            substitute(substitute(pc1, subst[0]), {k: k}),
            substitute(substitute(pc2, subst[1]), {k: k + Int(1)}),
        ]

        # Conflict Formula
        W1 = substitute_subset(
            substitute_subset(comp1.get_write_set(), subst[0]), {k: k}
        )
        R1 = substitute_subset(
            substitute_subset(comp1.get_read_set(), subst[0]), {k: k}
        )
        W2 = substitute_subset(
            substitute_subset(comp2.get_write_set(), subst[1]),
            {k: k + Int(1)},
        )
        R2 = substitute_subset(
            substitute_subset(comp2.get_read_set(), subst[1]),
            {k: k + Int(1)},
        )
        conflicts = [
            _create_set_intersection_formula(W1, R2, id_to_val_symbol_map),
            _create_set_intersection_formula(W1, W2, id_to_val_symbol_map),
            _create_set_intersection_formula(R1, W2, id_to_val_symbol_map),
        ]

        conflict_elements.append((existential_vars, path_conds, bounds, conflicts))

    return conflict_elements


def exists_data_forall_bounds_forall_iters_chained(
    loop_node: Loop,
    extra_assertions: list[PysmtFormula] | None = None,
    verbose: bool = True,
    build_negated: bool = False,
) -> str:
    """
    Generates an SMT query to prove that for a loop, there EXISTS a data
    configuration such that FORALL bounds and FORALL adjacent iterations, a
    dependency exists.

    If build_negated is True, a quantifier-free query is generated to check
    for the existence of a counterexample.
    """
    builder = SmtQueryBuilder()

    # Use the original loop variable from the P3G model for the analysis
    k = loop_node.loop_var

    # 1. Define Universal Quantifiers
    builder.add_universal_var(k)
    bounds_vars = _get_free_variables_recursive(
        loop_node.start
    ) | _get_free_variables_recursive(loop_node.end)
    for var in bounds_vars:
        builder.add_universal_var(var)

    # Store the set of universal variables that will be used in the main ForAll quantifier
    universal_vars_for_forall = builder._universal_vars.copy()

    # 2. Define symbols for analysis
    all_data_nodes: set[Data] = set()
    _collect_all_data_nodes(loop_node.builder.root_graph, all_data_nodes)

    # Create INT symbols for array locations (e.g., DATA!A), used for aliasing checks.
    id_to_location_symbol_map = {}
    processed_array_ids = set()  # To prevent redundant assertions for the same array_id
    for data_node in all_data_nodes:
        if data_node.array_id in processed_array_ids:
            continue
        processed_array_ids.add(data_node.array_id)

        array_name = data_node.graph._array_id_to_name[data_node.array_id]
        # This symbol represents the array's identity/location.
        loc_sym = Symbol(f"DATA!{array_name}", INT)
        id_to_location_symbol_map[data_node.array_id] = loc_sym
        # Define this location symbol as a constant at the top level.
        builder.add_toplevel_assertion(Equals(loc_sym, Int(data_node.array_id)))

    # Note: Symbols for array *values* (e.g., A_val) are not created here.
    # They are discovered automatically by the SmtQueryBuilder if they appear
    # in any of the formulas being serialized, and are treated as free existential variables.

    # 3. Build the Antecedent (LHS of =>)
    builder.add_antecedent_clause(GE(loop_node.end, Plus(loop_node.start, Int(1))))
    builder.add_antecedent_clause(GE(k, loop_node.start))
    builder.add_antecedent_clause(LE(Plus(k, Int(1)), loop_node.end))

    # Add any assertions from the parsed code, separating into toplevel or antecedent
    all_graph_assertions = []
    _collect_all_assertions_recursive(
        loop_node.builder.root_graph, all_graph_assertions
    )
    for assertion in all_graph_assertions:
        assertion_free_vars = get_free_variables(assertion)
        if any(v in universal_vars_for_forall for v in assertion_free_vars):
            # Assertion depends on universal variables, keep in antecedent
            builder.add_antecedent_clause(assertion)
        else:
            # Assertion does not depend on universal variables, move to toplevel
            builder.add_toplevel_assertion(assertion)

    if extra_assertions:
        for assertion in extra_assertions:
            assertion_free_vars = get_free_variables(assertion)
            if any(v in universal_vars_for_forall for v in assertion_free_vars):
                builder.add_antecedent_clause(assertion)
            else:
                builder.add_toplevel_assertion(assertion)

    # 4. Populate the Consequent (RHS of =>) with dependency clauses
    # Collect all conjuncts for the pair clause and filter out TRUE literals
    for existential_vars, path_conds, bounds, conflicts in _find_conflict_elements(
        loop_node.nested_graph, k, id_to_location_symbol_map
    ):
        all_conjuncts = [*bounds, *path_conds, Or(*conflicts)]
        if existential_vars:
            clause = Exists(
                sorted(list(existential_vars), key=lambda s: s.symbol_name()),
                simplify(And(all_conjuncts)),
            )
        else:
            clause = simplify(And(all_conjuncts))
        builder.add_consequent_clause(clause)

        # In the negated version, we don't want a witness outside the valid bound.
        if build_negated:
            for b in bounds:
                builder.add_antecedent_clause(b)

    # 5. Assemble and return the final query
    if build_negated:
        smt_query = builder.build_negated_query()
        if verbose:
            print(f"--- SMT v2 Query (Negated) ---\n{smt_query}")
    else:
        smt_query = builder.build_query()
        if verbose:
            print(f"--- SMT v2 Query (Chained) ---\n{smt_query}")

    return smt_query


def _collect_all_assertions_recursive(graph: Graph, collected_assertions: list):
    """Recursively collects all assertion formulas from the graph hierarchy."""
    collected_assertions.extend(graph.assertions)
    for node in graph.nodes:
        if isinstance(node, Branch):
            for _, nested_graph in node.branches:
                _collect_all_assertions_recursive(nested_graph, collected_assertions)
        elif isinstance(node, Loop):
            _collect_all_assertions_recursive(node.nested_graph, collected_assertions)


def _collect_all_data_nodes(graph: Graph, collected_data_nodes: set[Data]):
    """Recursively collects all Data nodes from the graph and its nested structures."""
    for node in graph.nodes:
        if isinstance(node, Data):
            collected_data_nodes.add(node)
        elif isinstance(node, Branch):
            for _, nested_graph in node.branches:
                _collect_all_data_nodes(nested_graph, collected_data_nodes)
        elif isinstance(node, Loop):
            _collect_all_data_nodes(node.nested_graph, collected_data_nodes)
