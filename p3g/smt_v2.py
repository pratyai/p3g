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

from pysmt.rewritings import NNFizer
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
    Implies,
    get_free_variables,
    substitute,
    TRUE,
    FALSE,
    simplify,
    Not,
)
from pysmt.smtlib.printers import SmtPrinter
from pysmt.typing import INT

from p3g.graph import Graph, Loop, Data, Compute, Branch, Map, Reduce
from p3g.subsets import (
    _create_set_intersection_formula,
    substitute_subset,
    PysmtFormula,
    _get_free_variables_recursive,
    PysmtSymbol,
)

ComputeItem = namedtuple("ComputeItem", ["path_cond", "compute_node", "loops"])


class AnalysisContext:
    """
    A data structure to pre-gather and store all necessary information from the P3G
    for SMT query generation, avoiding repeated graph traversals.
    """

    def __init__(self):
        #: A set of all Data nodes found throughout the entire graph hierarchy.
        self.all_data_nodes: set[Data] = set()
        #: Maps each unique array_id to its original name (e.g., 10001 -> "A").
        self.id_to_array_name: dict[int, str] = {}
        #: Maps each unique array_id to a PysmtSymbol representing its memory location
        #: (e.g., 10001 -> Symbol("DATA!A", INT)). Used for aliasing checks.
        self.id_to_location_symbol_map: dict[int, PysmtSymbol] = {}
        #: Maps a PysmtSymbol representing an array's content (e.g., Symbol("A_val", ArrayType))
        #: to its corresponding internal array_id.
        self.pysmt_array_sym_to_array_id: dict[PysmtSymbol, int] = {}
        #: A flattened list of all ComputeItem (path_cond, compute_node, loops) tuples
        #: within the specified Loop node's body.
        self.all_compute_items: list[ComputeItem] = []
        #: A list of all PysmtFormula assertions collected from the graph, including
        #: ancestral assertions and nested loop non-empty checks.
        self.all_assertions: list[PysmtFormula] = []
        #: A set of PysmtSymbols that appear in the start and end bounds of any
        #: Loop node within the graph hierarchy, excluding loop iterators themselves.
        self.loop_bound_symbols: set[PysmtSymbol] = set()
        #: A set of PysmtSymbols identified as universally quantified variables
        #: in the SMT query (e.g., outer loop iterators, global parameters).
        self.universal_vars: set[PysmtSymbol] = set()
        #: A list of additional PysmtFormula assertions provided by the user.
        self.extra_assertions: list[PysmtFormula] = []


class SmtQueryBuilder:
    """A structured builder for the specific SMT query pattern needed."""

    def __init__(self, logic: str | None = None):
        self.logic = logic
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

    def _format_type(self, t) -> str:
        """Converts PySMT type to SMT-LIB string representation."""
        if t.is_int_type():
            return "Int"
        if t.is_bool_type():
            return "Bool"
        if t.is_array_type():
            return f"(Array {self._format_type(t.index_type)} {self._format_type(t.elem_type)})"
        return str(t)

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
                [
                    f"({s.symbol_name()} {self._format_type(s.get_type())})"
                    for s in quantified_vars
                ]
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
        # We simplify components first, but assume Implies structure is desired for output
        # (especially for CHC/Horn clauses where '=>' is standard).
        antecedent = (
            And(self._antecedent_clauses) if self._antecedent_clauses else TRUE()
        )
        consequent = (
            Or(self._consequent_clauses) if self._consequent_clauses else FALSE()
        )

        ant_simp = simplify(antecedent)
        cons_simp = simplify(consequent)

        # Filter universals to only those actually used in the simplified formula
        sorted_universals = sorted(
            list(self._universal_vars), key=lambda s: s.symbol_name()
        )

        # Construct Implies. Note: We do NOT call simplify() on the final structure
        # because pysmt simplifies Implies(A, B) into Or(Not(A), B), which we want
        # to avoid to preserve the '(=> ...)' syntax for CHC solvers.
        main_formula = ForAll(
            sorted_universals, Implies(simplify(And(ant_simp, Not(cons_simp))), FALSE())
        )

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

        header_lines = sorted([get_decl_str(d) for d in final_existentials], key=str)

        output_lines = []
        if self.logic:
            output_lines.append(f"(set-logic {self.logic})")

        output_lines.extend(header_lines)

        all_assertions_parts = []
        if toplevel_assertion_strs:
            all_assertions_parts.append("\n".join(toplevel_assertion_strs))
            all_assertions_parts.append("")  # Add the empty line here
        all_assertions_parts.append(main_assertion_str)

        all_assertions = "\n".join(all_assertions_parts)

        return "\n".join(output_lines) + f"\n\n{all_assertions}\n\n(check-sat)"

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
        assert main_formula.is_exists() or main_formula.is_false()
        if main_formula.is_exists():
            (main_formula,) = main_formula.args()

        # Step 2: Collect all free variables
        local_free_vars = self._existential_vars.copy()

        def collect_free_vars_local(formula: PysmtFormula):
            if formula is None:
                return
            for sym in get_free_variables(formula):
                if sym not in self._universal_vars:
                    local_free_vars.add(sym)

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
        final_existentials = local_free_vars - self._universal_vars
        vars_to_quantify = {
            v for v in final_existentials if v.symbol_name().endswith("_val")
        }
        vars_to_declare = final_existentials - vars_to_quantify

        def get_decl_str(s: PysmtSymbol) -> str:
            t = s.get_type()
            if t.is_int_type():
                return f"(declare-fun {s.symbol_name()} () Int)"
            if t.is_array_type():
                return f"(declare-fun {s.symbol_name()} () (Array {t.index_type} {t.elem_type}))"
            return f"(declare-fun {s.symbol_name()} () {t})"

        header_lines = sorted([get_decl_str(d) for d in vars_to_declare], key=str)

        output_lines = []
        if self.logic:
            output_lines.append(f"(set-logic {self.logic})")

        output_lines.extend(header_lines)

        # Combine assertions and wrap in ForAll if needed
        # We must split assertions: those depending on quantified vars (data) must act as
        # implications (antecedents), while those strictly on free vars (params) must
        # remain assertions (conjunctions) to prevent trivial satisfaction by invalid params.
        data_dependent_asserts = []
        global_asserts = []

        for assertion in simplified_toplevel_assertions:
            # Check if assertion depends on any variable we are about to quantify
            if get_free_variables(assertion) & vars_to_quantify:
                data_dependent_asserts.append(assertion)
            else:
                global_asserts.append(assertion)

        # Construct the inner formula: (DataAsserts => MainFormula)
        inner_formula = main_formula
        if data_dependent_asserts:
            inner_formula = Implies(And(data_dependent_asserts), inner_formula)

        # Wrap in ForAll if we have variables to quantify
        if vars_to_quantify:
            sorted_vars = sorted(list(vars_to_quantify), key=lambda s: s.symbol_name())
            quantified_formula = ForAll(sorted_vars, inner_formula)
        else:
            quantified_formula = inner_formula

        # Combine with global parameter assertions: GlobalAsserts AND QuantifiedFormula
        combined_formula = And(global_asserts + [quantified_formula])

        final_assertion_str = f"(assert {self._pretty_print(combined_formula, 0)})"

        return "\n".join(output_lines) + f"\n\n{final_assertion_str}\n\n(check-sat)"


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
                        GE(
                            v,
                            substitute(
                                substitute(loop.start, {k: k + Int(offset)}),
                                subst[offset],
                            ),
                        ),
                        LE(
                            v,
                            substitute(
                                substitute(loop.end, {k: k + Int(offset)}),
                                subst[offset],
                            ),
                        ),
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


def _build_analysis_context(
    root_graph: Graph,
    loop_node: Loop,
    extra_assertions: list[PysmtFormula] | None = None,
) -> AnalysisContext:
    """
    Traverses the P3G and gathers all necessary information into an AnalysisContext object.
    """
    context = AnalysisContext()
    context.extra_assertions = extra_assertions if extra_assertions is not None else []
    # Add extra_assertions to all_assertions for comprehensive collection
    context.all_assertions.extend(context.extra_assertions)

    # Helper recursive function for graph traversal
    def _traverse_graph(
        graph: Graph,
        target_loop: Loop,
        builder_instance,  # The GraphBuilder instance from loop_node.builder
        current_assertions: list[
            PysmtFormula
        ],  # Accumulates assertions from ancestor graphs
        is_target_loop_ancestor_or_self: bool,  # True if 'graph' is the target loop or one of its ancestors
    ):
        # Add assertions explicitly defined at the current graph level
        context.all_assertions.extend(graph.assertions)

        # Collect data node information
        for node in graph.nodes:
            if isinstance(node, Data):
                context.all_data_nodes.add(node)
                if node.array_id not in context.id_to_array_name:
                    context.id_to_array_name[node.array_id] = (
                        node.graph._array_id_to_name.get(node.array_id, node.name)
                    )
                    context.id_to_location_symbol_map[node.array_id] = Symbol(
                        f"DATA!{context.id_to_array_name[node.array_id]}", INT
                    )

                # Populate pysmt_array_sym_to_array_id from the builder's map
                # The builder's map directly maps array symbols to array_ids.
                # We iterate over the builder's map to copy relevant entries.
                for (
                    pysmt_sym,
                    arr_id,
                ) in (
                    builder_instance._pysmt_array_sym_to_array_id.items()
                ):  # Use builder_instance
                    if (
                        arr_id == node.array_id
                        and pysmt_sym not in context.pysmt_array_sym_to_array_id
                    ):
                        context.pysmt_array_sym_to_array_id[pysmt_sym] = arr_id

            # For Loop nodes, gather bounds, add non-empty checks, and identify universal vars
            elif isinstance(node, Loop):
                # Collect free variables from its start and end bounds
                free_vars = set(_get_free_variables_recursive(node.start))
                free_vars.update(_get_free_variables_recursive(node.end))
                for var in free_vars:
                    if var.get_type().is_int_type():
                        context.loop_bound_symbols.add(var)

                # Add non-empty assumption for the loop (start + 1 <= end)
                context.all_assertions.append(LE(Plus(node.start, Int(1)), node.end))

                _traverse_graph(
                    node.nested_graph,
                    target_loop,
                    builder_instance,  # Pass builder_instance down
                    current_assertions
                    + graph.assertions,  # Pass accumulated assertions to nested graph
                    is_target_loop_ancestor_or_self or node is target_loop,
                )

            # For Branch nodes, add branch predicate as assertion and traverse nested graphs
            elif isinstance(node, Branch):
                for pred, nested_graph in node.branches:
                    # The branch predicate defines the path condition, and should not be added to global assertions.
                    _traverse_graph(
                        nested_graph,
                        target_loop,
                        builder_instance,  # Pass builder_instance down
                        current_assertions
                        + graph.assertions
                        + [pred],  # Pass accumulated assertions to nested graph
                        is_target_loop_ancestor_or_self,
                    )

            # For Map and Reduce nodes, their nested graphs are traversed like Loop nodes.
            # No specific context collection other than the nested graph traversal.
            elif isinstance(
                node, (Map, Reduce)
            ):  # Assuming Map and Reduce also have nested_graph
                _traverse_graph(
                    node.nested_graph,
                    target_loop,
                    builder_instance,  # Pass builder_instance down
                    current_assertions + graph.assertions,
                    is_target_loop_ancestor_or_self,
                )

    # Start traversal from the root graph
    _traverse_graph(
        root_graph, loop_node, loop_node.builder, [], False
    )  # Pass loop_node.builder here

    # The target loop's iterator and its bounds variables are always universal
    context.universal_vars.add(loop_node.loop_var)
    bounds_vars = _get_free_variables_recursive(
        loop_node.start
    ) | _get_free_variables_recursive(loop_node.end)
    for var in bounds_vars:
        context.universal_vars.add(var)

    # All scalar symbolic constants from the root graph that are also loop bound symbols are universal
    for sym_const in root_graph.symbols.values():
        if (
            sym_const.get_type().is_int_type()
            and sym_const in context.loop_bound_symbols
        ):
            context.universal_vars.add(sym_const)

    # Collect all compute items within the loop_node's nested graph body
    context.all_compute_items = _flatten_graph_to_compute_items(loop_node.nested_graph)

    return context


def exists_data_forall_bounds_forall_iters_chained(
    loop_node: Loop,
    extra_assertions: list[PysmtFormula] | None = None,
    verbose: bool = True,
    build_negated: bool = False,
    logic: str | None = None,
) -> str:
    """
    Generates an SMT query to prove that for a loop, there EXISTS a data
    configuration such that FORALL loop bounds and FORALL adjacent iterations, a
    dependency is present.

    If build_negated is True, a quantifier-free query is generated to check
    for the existence of a counterexample.
    """
    builder = SmtQueryBuilder(logic=logic)

    # Build the analysis context
    context = _build_analysis_context(
        loop_node.builder.root_graph, loop_node, extra_assertions
    )

    # Use the original loop variable from the P3G model for the analysis
    k = loop_node.loop_var

    # 1. Define Universal Quantifiers from context
    for var in context.universal_vars:
        builder.add_universal_var(var)

    # Store the set of universal variables that will be used in the main ForAll quantifier
    universal_vars_for_forall = builder._universal_vars.copy()

    # 2. Use id_to_location_symbol_map from context for aliasing checks
    id_to_location_symbol_map = context.id_to_location_symbol_map

    # 3. Build the Antecedent (LHS of =>)
    builder.add_antecedent_clause(GE(loop_node.end, Plus(loop_node.start, Int(1))))
    builder.add_antecedent_clause(GE(k, loop_node.start))
    builder.add_antecedent_clause(LE(Plus(k, Int(1)), loop_node.end))

    # Add assertions from the analysis context, separating into toplevel or antecedent
    for assertion in context.all_assertions:
        assertion_free_vars = get_free_variables(assertion)
        if assertion_free_vars.issubset(universal_vars_for_forall):
            builder.add_antecedent_clause(assertion)

    # 4. Populate the Consequent (RHS of =>) with dependency clauses
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

        if build_negated:
            for b in bounds:
                if get_free_variables(b).issubset(universal_vars_for_forall):
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
