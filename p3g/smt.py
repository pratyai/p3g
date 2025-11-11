import io
from typing import List, Dict, Tuple, Set

from pysmt.shortcuts import (
    Symbol, INT, Equals,
    And, TRUE, Plus, Int, get_free_variables, FALSE, Or, GE, LE
)
from pysmt.smtlib.printers import SmtPrinter

# --- Import P3G model classes ---
from p3g.p3g import (
    Graph, Loop, Data, Compute, Branch, Map, PysmtFormula, PysmtSymbol,
    ReadSet, WriteSet, create_path_model_fn, Reduce
)

# Define __all__ for 'from p3g_smt import *'
__all__ = [
    'generate_smt_for_disprove_dofs',
    'generate_smt_for_prove_exists_data_forall_iter_isdep'
]


# --- SMT String Generation (unchanged) ---

class _StringSmtBuilder:
    """
    Helper class to build an SMT-LIB string query.
    Uses pysmt.SmtPrinter ONLY for serializing formulas.
    """

    def __init__(self):
        self.declarations = set()
        self.assertions = []
        self._string_io = io.StringIO()
        self._printer = SmtPrinter(self._string_io)

    def _serialize(self, formula: PysmtFormula) -> str:
        """Serializes a pysmt formula object into an SMT-LIB string."""
        for sym in get_free_variables(formula):
            self.declarations.add(sym)
        self._printer.printer(formula)
        s = self._string_io.getvalue()
        self._string_io.seek(0)
        self._string_io.truncate(0)
        return s

    def _get_decl_str(self, symbol: PysmtSymbol) -> str:
        """Gets the (declare-fun ...) string for a symbol."""
        if symbol.get_type().is_int_type():  # Explicitly handle INT type first
            return f"(declare-fun {symbol.symbol_name()} () Int)"
        elif symbol.get_type().is_function_type():
            param_types = " ".join([str(p) for p in symbol.get_type().param_types])
            return_type = symbol.get_type().return_type
            return f"(declare-fun {symbol.symbol_name()} ({param_types}) {return_type})"
        elif symbol.get_type().is_array_type():
            idx_type = symbol.get_type().index_type
            data_type = symbol.get_type().elem_type
            return f"(declare-fun {symbol.symbol_name()} () (Array {idx_type} {data_type}))"
        else:
            return f"(declare-fun {symbol.symbol_name()} () {symbol.get_type()})"

    def add_assertion(self, formula: PysmtFormula, comment: str):
        """Adds a standard (assert ...) command."""
        smt_str = self._serialize(formula)
        self.assertions.append(f"\n; {comment}")
        self.assertions.append(f"(assert {smt_str})")

    def add_let_assertion(self,
                          let_bindings: List[Tuple[str, str, str]],
                          main_formula_str: str,
                          main_comment: str):
        """
        Adds a single, complex assertion using a multi-line,
        indented 'let' block, built from raw strings.

        let_bindings is a list of (name, formula_string, comment)
        """
        self.assertions.append(f"\n; {main_comment}")
        self.assertions.append("(assert (let (")

        for (name, formula_str, comment) in let_bindings:
            if comment:
                self.assertions.append(f"  ; {comment}")

            self.assertions.append(f"  ({name} {formula_str})")
            self.assertions.append("")  # Add a blank line

        self.assertions.append(")")  # Close let bindings
        self.assertions.append(f"  ; Main formula")
        self.assertions.append(f"  {main_formula_str}")
        self.assertions.append("))")  # Close let and assert

    def build_query(self) -> str:
        """Assembles and returns the final SMT-LIB query string."""
        header = []
        for decl in sorted(list(self.declarations), key=lambda s: s.symbol_name()):
            header.append(self._get_decl_str(decl))

        body = "\n".join(self.assertions)
        footer = "\n\n(check-sat)\n"  # Removed (get-model)

        return "\n".join(header) + "\n" + body + footer


def _get_index_from_access(access_expr: PysmtFormula) -> PysmtFormula:
    """Helper to extract the index from a Select or Store operation."""
    if isinstance(access_expr, tuple):
        pass
    if access_expr.is_select():
        return access_expr.arg(1)
    elif access_expr.is_store():
        return access_expr.arg(1)
    else:
        return access_expr  # It's already an index expression


def _equal_indices(idx1, idx2):
    """
    Creates a pysmt formula asserting index equality.
    Handles single indices and multi-dimensional index tuples/lists.
    """
    is_idx1_tuple = isinstance(idx1, (tuple, list))
    is_idx2_tuple = isinstance(idx2, (tuple, list))

    if is_idx1_tuple and is_idx2_tuple:
        # Both are multi-dimensional: indices must be tuples of the same length
        if len(idx1) != len(idx2):
            return FALSE() # Different dimensions, cannot be equal

        # Create a conjunction (AND) of equality checks for each dimension
        equalities = [Equals(_get_index_from_access(i1), _get_index_from_access(i2)) for i1, i2 in zip(idx1, idx2)]
        if not equalities:
            return TRUE()  # Should not happen for arrays, but handle empty tuples
        return And(equalities)
    elif not is_idx1_tuple and not is_idx2_tuple:
        # Both are single dimension
        return Equals(_get_index_from_access(idx1), _get_index_from_access(idx2))
    else:
        # One is single dimension, the other is multi-dimension. Cannot be equal.
        return FALSE()


def _intersect_to_formula(set_a: ReadSet, set_b: WriteSet,
                          id_to_symbol_map: Dict[int, PysmtSymbol]) -> PysmtFormula:
    """Creates a pysmt formula for the intersection of two sets."""
    clauses = []
    if not set_a or not set_b:
        return FALSE()

    for (arr_a, idx_a) in set_a:
        for (arr_b, idx_b) in set_b:
            arr_a_node = id_to_symbol_map[arr_a]
            arr_b_node = id_to_symbol_map[arr_b]

            # Use the helper function to correctly handle multi-dimensional indices
            index_equality = _equal_indices(idx_a, idx_b)

            clauses.append(And(Equals(arr_a_node, arr_b_node), index_equality))

    if len(clauses) == 0:
        return FALSE()
    elif len(clauses) == 1:
        return clauses[0]
    else:
        return Or(clauses)


# Helper for recursive free variable extraction (needed for multi-dimensional access tuples)
def _get_free_variables_recursive(formula_or_tuple: [PysmtFormula, tuple, list]) -> Set[PysmtSymbol]:
    """Recursively extracts free variables from a formula or a tuple/list of formulas."""

    if isinstance(formula_or_tuple, (tuple, list)):
        # Recursive case: Traverse all elements in the multi-dimensional index tuple/list
        free_vars = set()
        for item in formula_or_tuple:
            free_vars.update(_get_free_variables_recursive(item))
        return free_vars
    else:
        # Base case: The item is a PysmtFormula
        return get_free_variables(formula_or_tuple)


def _collect_all_data_nodes(graph: Graph, collected_data_nodes: Set[Data]):
    """Recursively collects all Data nodes from the graph and its nested structures."""
    for node in graph.nodes:
        if isinstance(node, Data):
            collected_data_nodes.add(node)
        elif isinstance(node, Branch):
            for _, nested_graph in node.branches:
                _collect_all_data_nodes(nested_graph, collected_data_nodes)
        elif isinstance(node, (Loop, Map, Reduce)):
            _collect_all_data_nodes(node.nested_graph, collected_data_nodes)


def find_data_symbols(graph: Graph, collected_symbols: Set[PysmtSymbol]):
    """
    Recursively traverses the given P3G graph and collects all free PysmtSymbol
    objects found within the access patterns (subsets) of Compute nodes and
    predicates of Branch nodes.

    These collected symbols represent variables that influence data access
    or control flow, such as array indices, loop bounds, or symbolic constants
    used in predicates.

    The function adds all discovered free symbols to the `collected_symbols` set,
    regardless of their Pysmt type (e.g., INT, ArrayType, FunctionType).

    Args:
        graph: The P3G graph (or sub-graph) to traverse.
        collected_symbols: A mutable set to which discovered PysmtSymbol objects
                           will be added.
    """
    for node in graph.nodes:
        if isinstance(node, Compute):
            access_sets = node.get_read_set() + node.get_write_set()
            for arr_id, subset in access_sets:
                for free_var in _get_free_variables_recursive(subset):
                    collected_symbols.add(free_var)
        elif isinstance(node, Branch):
            for pred, g in node.branches:
                for free_var in _get_free_variables_recursive(pred):
                    collected_symbols.add(free_var)
                find_data_symbols(g, collected_symbols)
        elif isinstance(node, (Loop, Map)):
            find_data_symbols(node.nested_graph, collected_symbols)


def generate_smt_for_disprove_dofs(loop_node: Loop,
                                   loop_end: PysmtFormula,
                                   extra_assertions: List[
                                       PysmtFormula] = None) -> str:  # MODIFIED: Accept extra_assertions
    """
    Generates the SMT-LIB query string for disproving Data-Oblivious
    Full Sequentiality (Φ_¬DOFS).
    """

    id_to_symbol_map: Dict[int, PysmtSymbol] = {}
    # root_graph = loop_node.builder.root_graph # No longer needed directly here

    all_data_nodes: Set[Data] = set()
    _collect_all_data_nodes(loop_node.builder.root_graph, all_data_nodes) # Collect from the entire graph

    builder.assertions.append("; --- Data Definitions ---")
    for node in all_data_nodes: # Iterate over all collected Data nodes
        sym = Symbol(f"DATA!{node.name}", INT)
        id_to_symbol_map[node.array_id] = sym
        defn = Equals(sym, Int(node.array_id))
        builder.add_assertion(defn, f"Define DATA!{node.name}")

    k = loop_node.loop_var  # Use the loop's internal iteration variable
    j = Plus(k, Int(1))  # Define j relative to k

    # NEW BLOCK: Add human-provided assertions
    if extra_assertions:
        builder.assertions.append("\n; --- Human-Provided Bounds/Assertions ---")
        for idx, assertion in enumerate(extra_assertions):
            builder.add_assertion(assertion, f"Human Assertion #{idx}")

    builder.assertions.append("\n; --- Loop Bounds ---")
    loop_start, loop_end = loop_node.start, loop_node.end

    builder.add_assertion(
        GE(loop_end, Plus(loop_start, Int(1))),
        "Loop runs at least two adjacent iterations"
    )
    builder.add_assertion(GE(k, loop_start), "Iteration 'k' lower bound")
    builder.add_assertion(LE(j, loop_end), "Iteration 'k+1' upper bound")

    path_model_fn = create_path_model_fn(loop_node)
    paths_k = path_model_fn(k)
    paths_j = path_model_fn(j)

    builder.assertions.append("\n; --- Dependency Logic Definitions ---")

    let_bindings_tuples = []
    dep_var_names = []

    data_symbols_to_quantify = set()
    find_data_symbols(loop_node.nested_graph, data_symbols_to_quantify)

    for idx_k, (pred_k, W_k, R_k) in enumerate(paths_k):
        for idx_j, (pred_j, W_j, R_j) in enumerate(paths_j):
            waw = _intersect_to_formula(W_k, W_j, id_to_symbol_map)
            raw = _intersect_to_formula(W_k, R_j, id_to_symbol_map)
            war = _intersect_to_formula(R_k, W_j, id_to_symbol_map)

            waw_var = f"p{idx_k}p{idx_j}_waw"
            raw_var = f"p{idx_k}p{idx_j}_raw"
            war_var = f"p{idx_k}p{idx_j}_war"

            waw_str = builder._serialize(waw)
            raw_str = builder._serialize(raw)
            war_str = builder._serialize(war)

            path_pair_conflict_str = f"(or {waw_var} {raw_var} {war_var})"

            conflict_let_str = (
                f"(let (({waw_var} {waw_str})\n"
                f"        ({raw_var} {raw_str})\n"
                f"        ({war_var} {war_str}))\n"
                f"   {path_pair_conflict_str})"
            )

            pred_k_str = builder._serialize(pred_k)
            pred_j_str = builder._serialize(pred_j)

            full_path_dependency_str = (
                f"(and {pred_k_str}\n"
                f"     {pred_j_str}\n"
                f"     {conflict_let_str})"
            )

            dep_var_name = f"p{idx_k}p{idx_j}_dep"

            let_bindings_tuples.append(
                (dep_var_name, full_path_dependency_str, f"p{idx_k}(k) <-> p{idx_j}(j) dependency"))
            dep_var_names.append(dep_var_name)

    main_body_str = "(or\n" + "\n".join([f"    {name}" for name in dep_var_names]) + "\n  )"

    let_body_str = (
            f"(let (\n" +
            "\n".join([f"  ; {c}\n  ({n} {f})\n" for n, f, c in let_bindings_tuples]) +
            f")\n" +
            f"  ; Main formula\n" +
            f"  (not {main_body_str})\n" +
            ")"
    )

    builder.assertions.append("\n; Find a universal counterexample (for all data configs)")

    quantifier_vars = []
    for sym in data_symbols_to_quantify:
        # Exclude the SMT solver's iteration variables (which are now k and j)
        if sym == k or sym == j:
            continue

        # Exclude free variables from loop bound formulas
        # These are considered constants for the SMT solver, not universally quantified.
        for free_var_in_bound in _get_free_variables_recursive(loop_node.start):
            if sym == free_var_in_bound: continue
        for free_var_in_bound in _get_free_variables_recursive(loop_node.end):
            if sym == free_var_in_bound: continue

        # Exclude loop bound variables
        # Note: loop_node.start and loop_node.end might be complex formulas,
        # so direct equality check might not be sufficient if they are not simple Symbols.
        # For now, we assume they are simple Symbols or Ints.
        if sym == loop_node.start or sym == loop_end:
            continue

        # Exclude symbols that are already defined as DATA! symbols
        # (these are handled by id_to_symbol_map and are not universally quantified here)
        # This check is implicitly handled by the fact that DATA! symbols are not in data_symbols_to_quantify
        # in the first place, as data_symbols_to_quantify only contains free variables from formulas.
        builder.declarations.add(sym)
        if sym.get_type().is_array_type():
            q_type = f"(Array {sym.get_type().index_type} {sym.get_type().elem_type})"
        elif sym.get_type().is_function_type():
            param_types = " ".join([str(p) for p in sym.get_type().param_types])
            return_type = sym.get_type().return_type
            q_type = f"({param_types}) {return_type}"
        elif sym.get_type().is_int_type():  # Explicitly handle INT type
            q_type = f"{sym.get_type()}"
        else:
            q_type = f"{sym.get_type()}"  # Fallback

        quantifier_vars.append(f"({sym.symbol_name()} {q_type})")

    if quantifier_vars:
        builder.assertions.append("(assert (forall (")
        builder.assertions.extend([f"  {q}" for q in quantifier_vars])
        builder.assertions.append(") ; End of quantified variables")
        for line in let_body_str.split('\n'):
            builder.assertions.append(f"  {line}")
        builder.assertions.append("))")  # Close forall and assert
    else:
        # No data symbols, just assert the 'let' block
        builder.assertions.append(f"(assert {let_body_str})")

    return builder.build_query()


def generate_smt_for_prove_exists_data_forall_iter_isdep(
        loop_node: Loop,
        loop_end: PysmtFormula,
        extra_assertions: List[PysmtFormula] = None,
        verbose: bool = True) -> str:  # MODIFIED: Accept extra_assertions
    """
    Generates the SMT-LIB query string for disproving Data-Oblivious
    Full Sequentiality (Φ_¬DOFS).
    """

    k = loop_node.loop_var  # Use the loop's internal iteration variable
    j = Plus(k, Int(1))  # Define j relative to k

    data_symbols_to_quantify = set()
    find_data_symbols(loop_node.nested_graph, data_symbols_to_quantify)

    existential_quantifier_vars = []
    for sym in data_symbols_to_quantify:
        # Exclude free variables from loop bound formulas
        # These are considered constants for the SMT solver, not universally quantified.
        for free_var_in_bound in _get_free_variables_recursive(loop_node.start):
            if sym == free_var_in_bound: continue
        for free_var_in_bound in _get_free_variables_recursive(loop_node.end):
            if sym == free_var_in_bound: continue

        # Exclude loop bound variables
        # Note: loop_node.start and loop_node.end might be complex formulas,
        # so direct equality check might not be sufficient if they are not simple Symbols.
        # For now, we assume they are simple Symbols or Ints.
        if sym == loop_node.start or sym == loop_end:
            continue

        # Exclude the SMT solver's iteration variables (which are now k and j)
        if sym == k or sym == j:
            continue

        # Exclude symbols that are already defined as DATA! symbols
        # (these are handled by id_to_symbol_map and are not universally quantified here)
        # This check is implicitly handled by the fact that DATA! symbols are not in data_symbols_to_quantify
        # in the first place, as data_symbols_to_quantify only contains free variables from formulas.
        existential_quantifier_vars.append(sym)  # Store the PysmtSymbol directly

    universal_quantifier_vars = [f"({k.symbol_name()} {k.get_type()})"]

    builder = _StringSmtBuilder()

    # Declare existential quantifiers
    for sym in existential_quantifier_vars:
        builder.declarations.add(sym)

    # Declare universal quantifiers (k)
    builder.declarations.add(k)

    id_to_symbol_map: Dict[int, PysmtSymbol] = {}
    # root_graph = loop_node.builder.root_graph # No longer needed directly here

    all_data_nodes: Set[Data] = set()
    _collect_all_data_nodes(loop_node.builder.root_graph, all_data_nodes) # Collect from the entire graph

    builder.assertions.append("; --- Data Definitions ---")
    for node in all_data_nodes: # Iterate over all collected Data nodes
        sym = Symbol(f"DATA!{node.name}", INT)
        id_to_symbol_map[node.array_id] = sym
        defn = Equals(sym, Int(node.array_id))
        builder.add_assertion(defn, f"Define DATA!{node.name}")

    # NEW BLOCK: Add human-provided assertions
    if extra_assertions:
        builder.assertions.append("\n; --- Human-Provided Bounds/Assertions ---")
        for idx, assertion in enumerate(extra_assertions):
            builder.add_assertion(assertion, f"Human Assertion #{idx}")

    builder.assertions.append("\n; --- Loop Bounds ---")
    loop_start, loop_end = loop_node.start, loop_node.end

    builder.add_assertion(
        GE(loop_end, Plus(loop_start, Int(1))),
        "Loop runs at least two adjacent iterations"
    )

    path_model_fn = create_path_model_fn(loop_node)
    paths_k = path_model_fn(k)
    paths_j = path_model_fn(j)

    builder.assertions.append("\n; --- Dependency Logic Definitions ---")
    # builder.add_assertion(GE(k, loop_start), "Iteration 'k' lower bound")
    # builder.add_assertion(LE(j, loop_end), "Iteration 'k+1' upper bound")
    loop_runs_at_least_two_iterations = GE(loop_end, Plus(loop_start, Int(1)))
    k_lower_bound = GE(k, loop_start)
    j_upper_bound = LE(j, loop_end)

    let_bindings_tuples = []
    dep_var_names = []

    for idx_k, (pred_k, W_k, R_k) in enumerate(paths_k):
        for idx_j, (pred_j, W_j, R_j) in enumerate(paths_j):
            waw = _intersect_to_formula(W_k, W_j, id_to_symbol_map)
            raw = _intersect_to_formula(W_k, R_j, id_to_symbol_map)
            war = _intersect_to_formula(R_k, W_j, id_to_symbol_map)

            waw_var = f"p{idx_k}p{idx_j}_waw"
            raw_var = f"p{idx_k}p{idx_j}_raw"
            war_var = f"p{idx_k}p{idx_j}_war"

            waw_str = builder._serialize(waw)
            raw_str = builder._serialize(raw)
            war_str = builder._serialize(war)

            path_pair_conflict_str = f"(or {waw_var} {raw_var} {war_var})"

            conflict_let_str = f"""
(let (
    ({waw_var} {waw_str})
    ({raw_var} {raw_str})
    ({war_var} {war_str})
    ) {path_pair_conflict_str})
"""

            pred_k_str = builder._serialize(pred_k)
            pred_j_str = builder._serialize(pred_j)

            full_path_dependency_str = f"""
(and {pred_k_str} {pred_j_str} {conflict_let_str})
"""

            dep_var_name = f"p{idx_k}p{idx_j}_dep"

            let_bindings_tuples.append(
                (dep_var_name, full_path_dependency_str, f"p{idx_k}(k) <-> p{idx_j}(j) dependency"))
            dep_var_names.append(dep_var_name)

    main_body_str = "(or\n" + "\n".join([f"    {name}" for name in dep_var_names]) + "\n  )"

    let_bindings = "\n".join([f"; {c}\n({n} {f})" for n, f, c in let_bindings_tuples])

    loop_bound_str = f"""(and
    {builder._serialize(loop_runs_at_least_two_iterations)}
    {builder._serialize(k_lower_bound)}
    {builder._serialize(LE(Plus(k, Int(1)), loop_end))}
)"""
    # Construct the inner forall (k)
    inner_forall_str = f"""(forall ({" ".join(universal_quantifier_vars)}) ; End of universal variables
    (=> {loop_bound_str}
    (let (
        {let_bindings}
        )
        ; Main formula
        {main_body_str}
    )
))"""

    # if existential_quantifier_vars:
    #     builder.assertions.append("(assert (exists (")
    #     builder.assertions.extend([f"  ({sym.symbol_name()} {sym.get_type()})" for sym in existential_quantifier_vars])
    #     builder.assertions.append(") ; End of existential variables")
    #     for line in inner_forall_str.split('\n'):
    #         builder.assertions.append(f"  {line}")
    #     builder.assertions.append("))")  # Close exists and assert
    # else:
    # No existential quantifiers, just assert the inner forall
    builder.assertions.append(f"(assert {inner_forall_str})")

    smt_query =  builder.build_query()
    if verbose:
        print(f"""
{smt_query}
""")
    return smt_query
