import io
from typing import List, Dict, Set

from pysmt.shortcuts import (
    Symbol,
    INT,
    Equals,
    And,
    TRUE,
    Plus,
    Int,
    get_free_variables,
    FALSE,
    Or,
    GE,
    LE,
)
from pysmt.smtlib.printers import SmtPrinter

# --- Import P3G model classes ---
from p3g.p3g import (
    Graph,
    Loop,
    Data,
    Compute,
    Branch,
    Map,
    PysmtFormula,
    PysmtSymbol,
    ReadSet,
    WriteSet,
    create_path_model_fn,
    Reduce,
)


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
            return FALSE()  # Different dimensions, cannot be equal

        # Create a conjunction (AND) of equality checks for each dimension
        equalities = [
            Equals(_get_index_from_access(i1), _get_index_from_access(i2))
            for i1, i2 in zip(idx1, idx2)
        ]
        if not equalities:
            return TRUE()  # Should not happen for arrays, but handle empty tuples
        return And(equalities)
    elif not is_idx1_tuple and not is_idx2_tuple:
        # Both are single dimension
        return Equals(_get_index_from_access(idx1), _get_index_from_access(idx2))
    else:
        # One is single dimension, the other is multi-dimension. Cannot be equal.
        return FALSE()


def _intersect_to_formula(
    set_a: ReadSet, set_b: WriteSet, id_to_symbol_map: Dict[int, PysmtSymbol]
) -> PysmtFormula:
    """Creates a pysmt formula for the intersection of two sets."""
    clauses = []
    if not set_a or not set_b:
        return FALSE()

    for arr_a, idx_a in set_a:
        for arr_b, idx_b in set_b:
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


def _build_dependency_logic_assertions(
    loop_node: Loop,
    k: PysmtSymbol,
    builder: _StringSmtBuilder,
    id_to_symbol_map: Dict[int, PysmtSymbol],
) -> (str, str):
    """
    Builds the SMT-LIB assertions for the dependency logic between adjacent loop iterations.
    This includes generating let-bindings for WAW, RAW, WAR conflicts and the main OR body.

    Args:
        loop_node: The P3G Loop node being analyzed.
        k: The PysmtSymbol representing the current iteration variable.
        builder: The _StringSmtBuilder instance to serialize formulas.
        id_to_symbol_map: A map from array_id to PysmtSymbol for data arrays.

    Returns:
        A tuple containing (let_bindings_str, main_body_str).
    """
    path_model_fn = create_path_model_fn(loop_node)
    paths_k = path_model_fn(k)
    paths_j = path_model_fn(Plus(k, Int(1)))

    let_bindings_list = []
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

            let_bindings_list.append(f"; p{idx_k}(k) <-> p{idx_j}(j) dependency")
            let_bindings_list.append(f"({dep_var_name} {full_path_dependency_str})")
            let_bindings_list.append("")  # Add a blank line for readability

            dep_var_names.append(dep_var_name)

    main_body_str = (
        "(or\n" + "\n".join([f"    {name}" for name in dep_var_names]) + "\n  )"
    )

    let_bindings = "\n".join(let_bindings_list)
    return let_bindings, main_body_str


# Helper for recursive free variable extraction (needed for multi-dimensional access tuples)
def _get_free_variables_recursive(
    formula_or_tuple: [PysmtFormula, tuple, list],
) -> Set[PysmtSymbol]:
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


def _find_data_symbols(graph: Graph, collected_symbols: Set[PysmtSymbol]):
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
                _find_data_symbols(g, collected_symbols)
        elif isinstance(node, (Loop, Map)):
            _find_data_symbols(node.nested_graph, collected_symbols)


def _get_existential_quantifier_vars(
    loop_node: Loop, k: PysmtSymbol
) -> List[PysmtSymbol]:
    """
    Identifies and collects PysmtSymbol objects that need to be existentially
    quantified in the SMT query for DOFS analysis. These are typically data
    symbols that the solver can assign values to in order to find a
    sequentializing data configuration.

    Args:
        loop_node: The P3G Loop node being analyzed.
        k: The PysmtSymbol representing the current iteration variable.

    Returns:
        A list of PysmtSymbol objects to be existentially quantified.
    """
    data_symbols_to_quantify = set()
    _find_data_symbols(loop_node.nested_graph, data_symbols_to_quantify)

    existential_quantifier_vars = []
    for sym in data_symbols_to_quantify:
        # Exclude free variables from loop bound formulas
        # These are considered constants for the SMT solver, not universally quantified.
        for free_var_in_bound in _get_free_variables_recursive(loop_node.start):
            if sym == free_var_in_bound:
                continue
        for free_var_in_bound in _get_free_variables_recursive(loop_node.end):
            if sym == free_var_in_bound:
                continue

        # Exclude loop bound variables
        # Note: loop_node.start and loop_node.end might be complex formulas,
        # so direct equality check might not be sufficient if they are not simple Symbols.
        # For now, we assume they are simple Symbols or Ints.
        if sym == loop_node.start or sym == loop_node.end:
            continue

        # Exclude the SMT solver's iteration variables
        if sym == k:
            continue

        # Exclude symbols that are already defined as DATA! symbols
        # (these are handled by id_to_symbol_map and are not universally quantified here)
        # This check is implicitly handled by the fact that DATA! symbols are not in data_symbols_to_quantify
        # in the first place, as data_symbols_to_quantify only contains free variables from formulas.
        existential_quantifier_vars.append(sym)  # Store the PysmtSymbol directly
    return existential_quantifier_vars


def generate_smt_for_prove_exists_data_forall_iter_isdep(
    loop_node: Loop, extra_assertions: List[PysmtFormula] = None, verbose: bool = True
) -> str:
    """
    Generates an SMT-LIB query string to prove Data-Oblivious Full Sequentiality (Φ_DOFS)
    for a given loop.

    A loop is considered Data-Oblivious Full Sequential (DOFS) if there exists *at least one*
    specific assignment of values to its symbolic data arrays (a "data configuration")
    such that a data dependency is guaranteed to exist between *every* pair of adjacent
    iterations (k and k+1) within the loop's execution range.
    In simpler terms, a DOFS loop *cannot* be parallelized because there's at least one
    data scenario where dependencies always force sequential execution.

    The SMT query is constructed to find such a "sequentializing" data configuration.

    Interpretation of SMT Solver Results:
    - If the SMT solver returns `SAT` (Satisfiable), it means the query's assertion is true:
      it has found a data configuration for which a dependency exists between
      iterations `k` and `k+1` for all valid `k`.
      Therefore, the loop is **DOFS (Sequential)**.
    - If the SMT solver returns `UNSAT` (Unsatisfiable), it means the query's assertion is false:
      no such "sequentializing" data configuration exists. This implies that for *every*
      data configuration, there is at least one pair of adjacent iterations (k, k+1)
      that does *not* have a dependency.
      Therefore, the loop is **not DOFS (Parallel)**.

    Args:
        loop_node: The P3G Loop node for which to generate the SMT query.
        extra_assertions: An optional list of additional PysmtFormula assertions
                          to include in the SMT query. These can be used to
                          constrain symbolic variables (e.g., array sizes,
                          specific data values) for more targeted analysis.
        verbose: If True, prints the generated SMT query to stdout.

    Returns:
        A string containing the SMT-LIB query.
    """

    k = loop_node.loop_var  # Use the loop's internal iteration variable
    existential_quantifier_vars = _get_existential_quantifier_vars(loop_node, k)

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
    _collect_all_data_nodes(
        loop_node.builder.root_graph, all_data_nodes
    )  # Collect from the entire graph

    builder.assertions.append("; --- Data Definitions ---")
    for node in all_data_nodes:  # Iterate over all collected Data nodes
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
        "Loop runs at least two adjacent iterations",
    )

    builder.assertions.append("\n; --- Dependency Logic Definitions ---")
    loop_runs_at_least_two_iterations = GE(loop_end, Plus(loop_start, Int(1)))
    k_lower_bound = GE(k, loop_start)

    let_bindings, main_body_str = _build_dependency_logic_assertions(
        loop_node, k, builder, id_to_symbol_map
    )

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

    # No existential quantifiers, just assert the inner forall
    builder.assertions.append(f"(assert {inner_forall_str})")

    smt_query = builder.build_query()
    if verbose:
        print(f"""
{smt_query}
""")
    return smt_query


def generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isdep(
    loop_node: Loop, extra_assertions: List[PysmtFormula] = None, verbose: bool = True
) -> str:
    """
    Generates an SMT-LIB query string to prove Data-Oblivious Full Sequentiality (Φ_DOFS)
    for a given loop, with symbolic loop bounds explicitly universally quantified.

    This function is similar to `generate_smt_for_prove_exists_data_forall_iter_isdep`,
    but it explicitly includes any symbolic variables found in the loop's start and end
    bounds in the universal quantifier (`forall`) part of the SMT query. This means
    the solver will attempt to prove the property for *all possible integer values*
    of these symbolic loop bounds.

    A loop is considered Data-Oblivious Full Sequential (DOFS) if there exists *at least one*
    specific assignment of values to its symbolic data arrays (a "data configuration")
    such that a data dependency is guaranteed to exist between *every* pair of adjacent
    iterations (k and k+1) within the loop's execution range.
    In simpler terms, a DOFS loop *cannot* be parallelized because there's at least one
    data scenario where dependencies always force sequential execution.

    The SMT query is constructed to find such a "sequentializing" data configuration.

    Interpretation of SMT Solver Results:
    - If the SMT solver returns `SAT` (Satisfiable), it means the query's assertion is true:
      it has found a data configuration for which a dependency exists between
      iterations `k` and `k+1` for all valid `k` AND for all possible values of
      the symbolic loop bounds.
      Therefore, the loop is **DOFS (Sequential)**.
    - If the SMT solver returns `UNSAT` (Unsatisfiable), it means the query's assertion is false:
      no such "sequentializing" data configuration exists. This implies that for *every*
      data configuration, there is at least one pair of adjacent iterations (k, k+1)
      that does *not* have a dependency.
      Therefore, the loop is **not DOFS (Parallel)**.

    Args:
        loop_node: The P3G Loop node for which to generate the SMT query.
        extra_assertions: An optional list of additional PysmtFormula assertions
                          to include in the SMT query. These can be used to
                          constrain symbolic variables (e.g., array sizes,
                          specific data values) for more targeted analysis.
        verbose: If True, prints the generated SMT query to stdout.

    Returns:
        A string containing the SMT-LIB query.
    """

    k = loop_node.loop_var  # Use the loop's internal iteration variable
    existential_quantifier_vars = _get_existential_quantifier_vars(loop_node, k)

    # Identify symbolic loop bound variables
    symbolic_loop_bounds = set()
    for free_var in _get_free_variables_recursive(loop_node.start):
        if free_var != k:
            symbolic_loop_bounds.add(free_var)
    for free_var in _get_free_variables_recursive(loop_node.end):
        if free_var != k:
            symbolic_loop_bounds.add(free_var)

    universal_quantifier_vars = [f"({k.symbol_name()} {k.get_type()})"]
    for sym in symbolic_loop_bounds:
        universal_quantifier_vars.append(f"({sym.symbol_name()} {sym.get_type()})")

    builder = _StringSmtBuilder()

    # Declare existential quantifiers
    for sym in existential_quantifier_vars:
        builder.declarations.add(sym)

    # Declare universal quantifiers (k and symbolic loop bounds)
    builder.declarations.add(k)
    for sym in symbolic_loop_bounds:
        builder.declarations.add(sym)

    id_to_symbol_map: Dict[int, PysmtSymbol] = {}
    # root_graph = loop_node.builder.root_graph # No longer needed directly here

    all_data_nodes: Set[Data] = set()
    _collect_all_data_nodes(
        loop_node.builder.root_graph, all_data_nodes
    )  # Collect from the entire graph

    builder.assertions.append("; --- Data Definitions ---")
    for node in all_data_nodes:  # Iterate over all collected Data nodes
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
        "Loop runs at least two adjacent iterations",
    )

    builder.assertions.append("\n; --- Dependency Logic Definitions ---")
    loop_runs_at_least_two_iterations = GE(loop_end, Plus(loop_start, Int(1)))
    k_lower_bound = GE(k, loop_start)

    let_bindings, main_body_str = _build_dependency_logic_assertions(
        loop_node, k, builder, id_to_symbol_map
    )

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

    # No existential quantifiers, just assert the inner forall
    builder.assertions.append(f"(assert {inner_forall_str})")

    smt_query = builder.build_query()
    if verbose:
        print(f"""
{smt_query}
""")
    return smt_query

