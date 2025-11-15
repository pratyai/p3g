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
    LT,
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
        if formula.is_true():
            return "true"
        if formula.is_false():
            return "false"
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
        equalities = [Equals(i1, i2) for i1, i2 in zip(idx1, idx2)]
        if not equalities:
            return TRUE()  # Should not happen for arrays, but handle empty tuples
        return And(equalities)
    elif not is_idx1_tuple and not is_idx2_tuple:
        # Both are single dimension
        return Equals(idx1, idx2)
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

            if arr_a == arr_b:
                # Use the helper function to correctly handle multi-dimensional indices
                index_equality = _equal_indices(idx_a, idx_b)
                clauses.append(And(Equals(arr_a_node, arr_b_node), index_equality))
            # If arr_a != arr_b, we simply don't add a clause, as they cannot alias.

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
    return _build_dependency_logic_assertions_general(
        loop_node, k, Plus(k, Int(1)), builder, id_to_symbol_map
    )


def _build_dependency_logic_assertions_general(
    loop_node: Loop,
    iter_var1: PysmtSymbol,
    iter_var2: PysmtSymbol,
    builder: _StringSmtBuilder,
    id_to_symbol_map: Dict[int, PysmtSymbol],
) -> (str, str):
    """
    Builds the SMT-LIB assertions for the dependency logic between two arbitrary loop iterations.
    This includes generating let-bindings for WAW, RAW, WAR conflicts and the main OR body.

    Args:
        loop_node: The P3G Loop node being analyzed.
        iter_var1: The PysmtSymbol representing the first iteration variable.
        iter_var2: The PysmtSymbol representing the second iteration variable.
        builder: The _StringSmtBuilder instance to serialize formulas.
        id_to_symbol_map: A map from array_id to PysmtSymbol for data arrays.

    Returns:
        A tuple containing (let_bindings_str, main_body_str).
    """
    path_model_fn = create_path_model_fn(loop_node)
    paths_k = path_model_fn(iter_var1)
    paths_j = path_model_fn(iter_var2)

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

            # Store variables and their formulas for dynamic OR construction
            conflict_vars = [
                (waw_var, waw, waw),
                (raw_var, raw, raw),
                (war_var, war, war),
            ]

            # This list will contain ALL conflict variable names
            all_conflict_var_names = [name for name, _, _ in conflict_vars]

            # Construct the OR part of the conflict_let_str
            # Always construct an OR if there are any variables,
            # and simplify to 'false' only if there are no variables at all.
            if not all_conflict_var_names:
                path_pair_conflict_or_str = "false"
            elif len(all_conflict_var_names) == 1:
                path_pair_conflict_or_str = all_conflict_var_names[0]
            else:
                path_pair_conflict_or_str = f"(or {' '.join(all_conflict_var_names)})"

            # Construct the LET bindings for all variables (even if false)
            let_bindings_for_conflict = []
            for name, formula, _ in conflict_vars:
                let_bindings_for_conflict.append(
                    f"({name} {builder._serialize(formula)})"
                )

            pred_k_str = builder._serialize(pred_k)
            pred_j_str = builder._serialize(pred_j)

            # The conflict_let_str itself
            conflict_let_str = f"""
(let (
    {"\n    ".join(let_bindings_for_conflict)}
    ) {path_pair_conflict_or_str})
"""
            # Collect active components for the AND
            and_components = []
            if pred_k_str != "true":
                and_components.append(pred_k_str)
            if pred_j_str != "true":
                and_components.append(pred_j_str)

            # Only add conflict_let_str if it's not effectively "true"
            # A let expression (let (...) true) is logically equivalent to true.
            if path_pair_conflict_or_str != "true":
                and_components.append(conflict_let_str)

            if not and_components:
                full_path_dependency_str = "true"
            elif len(and_components) == 1:
                full_path_dependency_str = and_components[0]
            else:
                full_path_dependency_str = f"(and {' '.join(and_components)})"

            dep_var_name = f"p{idx_k}p{idx_j}_dep"

            let_bindings_list.append(f"; p{idx_k}(k) <-> p{idx_j}(j) dependency")
            let_bindings_list.append(f"({dep_var_name} {full_path_dependency_str})")
            let_bindings_list.append("")  # Add a blank line for readability

            dep_var_names.append(dep_var_name)

    if not dep_var_names:
        main_body_str = "false"
    elif len(dep_var_names) == 1:
        main_body_str = dep_var_names[0]
    else:
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


def generate_smt_for_prove_exists_data_exists_loop_bounds_exists_iter_isdep(
    loop_node: Loop, extra_assertions: List[PysmtFormula] = None, verbose: bool = True
) -> str:
    """
    Generates an SMT-LIB query to find if there exists a data configuration,
    loop bounds, and a pair of iterations (j, k) with j < k such that a
    data dependency exists.

    This is a more relaxed query than DOFS, aiming to find *any* dependency.
    It's often faster as it avoids universal quantifiers over loop bounds and iterations.

    Interpretation of SMT Solver Results:
    - SAT: A dependency was found for some data, loop bounds, and iterations.
           The loop is not fully parallel.
    - UNSAT: No dependency could be found. The loop is likely parallel.
    """

    k = loop_node.loop_var
    j = Symbol(f"{k.symbol_name()}_j", INT)

    builder = _StringSmtBuilder()

    # All variables (data, loop bounds, j, k) are effectively existentially quantified
    # by being free variables. We just need to declare them.

    builder.declarations.add(k)
    builder.declarations.add(j)

    # Collect data symbols that can be chosen by the solver
    existential_data_vars = _get_existential_quantifier_vars(loop_node, k)
    for sym in existential_data_vars:
        builder.declarations.add(sym)

    # Collect loop bound symbols
    symbolic_loop_bounds = set()
    for free_var in _get_free_variables_recursive(loop_node.start):
        if free_var != k and free_var != j:
            symbolic_loop_bounds.add(free_var)
    for free_var in _get_free_variables_recursive(loop_node.end):
        if free_var != k and free_var != j:
            symbolic_loop_bounds.add(free_var)
    for sym in symbolic_loop_bounds:
        builder.declarations.add(sym)

    # Collect defined data array symbols
    id_to_symbol_map: Dict[int, PysmtSymbol] = {}
    all_data_nodes: Set[Data] = set()
    _collect_all_data_nodes(loop_node.builder.root_graph, all_data_nodes)

    builder.assertions.append("; --- Data Definitions ---")
    for node in all_data_nodes:
        sym = Symbol(f"DATA!{node.name}", INT)
        id_to_symbol_map[node.array_id] = sym
        defn = Equals(sym, Int(node.array_id))
        builder.add_assertion(defn, f"Define DATA!{node.name}")

    if extra_assertions:
        builder.assertions.append("\n; --- Human-Provided Bounds/Assertions ---")
        for idx, assertion in enumerate(extra_assertions):
            builder.add_assertion(assertion, f"Human Assertion #{idx}")

    builder.assertions.append("\n; --- Loop Bounds ---")
    loop_start, loop_end = loop_node.start, loop_node.end

    # Assert loop runs at least two iterations
    builder.add_assertion(
        GE(loop_end, Plus(loop_start, Int(1))),
        "Loop runs at least two iterations",
    )

    # Assert j and k are within bounds and j < k
    j_lower_bound = GE(j, loop_start)
    j_upper_bound = LT(j, k)
    k_lower_bound = GE(k, loop_start)
    k_upper_bound = LE(k, loop_end)

    builder.add_assertion(
        And(j_lower_bound, j_upper_bound, k_lower_bound, k_upper_bound),
        "j < k within loop bounds",
    )

    builder.assertions.append("\n; --- Dependency Logic ---")
    let_bindings, main_body_str = _build_dependency_logic_assertions_general(
        loop_node, j, k, builder, id_to_symbol_map
    )

    dependency_formula_str = f"""
    (let (
        {let_bindings}
        )
        {main_body_str}
    )
    """
    builder.assertions.append(f"(assert {dependency_formula_str})")

    smt_query = builder.build_query()
    if verbose:
        print(f"\n-- Generated SMT for prove_dependency_existence --\n{smt_query}\n")
    return smt_query


def generate_smt_for_prove_exists_data_forall_iter_isindep(
    loop_node: Loop, extra_assertions: List[PysmtFormula] = None, verbose: bool = True
) -> str:
    """
    Generates an SMT-LIB query string to prove Data-Oblivious Full Independence (Φ_DOFI)
    for a given loop.

    A loop is considered Data-Oblivious Fully Independent (DOFI) if there exists *at least one*
    specific assignment of values to its symbolic data arrays (a "data configuration")
    such that *no* data dependency is guaranteed to exist between *any* pair of iterations
    (j and k, where j < k) within the loop's execution range.
    In simpler terms, a DOFI loop *can* be parallelized because there's at least one
    data scenario where no dependencies force sequential execution.

    The SMT query is constructed to find such a "parallelizing" data configuration.

    Interpretation of SMT Solver Results:
    - If the SMT solver returns `SAT` (Satisfiable), it means the query's assertion is true:
      it has found a data configuration for which *no* dependency exists between
      iterations `j` and `k` (where `j < k`) for all valid `j` and `k`.
      Therefore, the loop is **DOFI (Parallel)**.
    - If the SMT solver returns `UNSAT` (Unsatisfiable), it means the query's assertion is false:
      no such "parallelizing" data configuration exists. This implies that for *every*
      data configuration, there is at least one pair of iterations (j, k) with `j < k`
      that *does* have a dependency.
    """
    k = loop_node.loop_var  # Use the loop's internal iteration variable
    j = Symbol(f"{loop_node.loop_var.symbol_name()}_j", INT)  # New iteration variable j

    universal_quantifier_vars = [f"({k.symbol_name()} {k.get_type()})"]
    universal_quantifier_vars.append(f"({j.symbol_name()} {j.get_type()})")  # Add j

    builder = _StringSmtBuilder()

    # Declare universal quantifiers (k and j)
    builder.declarations.add(k)
    builder.declarations.add(j)  # Add j

    id_to_symbol_map: Dict[int, PysmtSymbol] = {}
    all_data_nodes: Set[Data] = set()
    _collect_all_data_nodes(
        loop_node.builder.root_graph, all_data_nodes
    )  # Collect from the entire graph

    builder.assertions.append("; --- Data Definitions ---")
    for node in all_data_nodes:  # Iterate over all collected Data nodes
        sym = Symbol(f"DATA!{node.name}", INT)
        id_to_symbol_map[node.array_id] = sym
        # Explicitly add DATA! symbols to declarations
        builder.declarations.add(sym)

    existential_quantifier_vars = list(id_to_symbol_map.values())

    # NEW BLOCK: Add human-provided assertions
    if extra_assertions:
        builder.assertions.append("\n; --- Human-Provided Bounds/Assertions ---")
        for idx, assertion in enumerate(extra_assertions):
            builder.add_assertion(assertion, f"Human Assertion #{idx}")

    builder.assertions.append("\n; --- Loop Bounds ---")
    loop_start, loop_end = loop_node.start, loop_node.end

    # The loop runs at least two iterations for j < k to be possible
    # builder.add_assertion( # Removed: part of loop_bound_formula now
    #     GE(loop_end, Plus(loop_start, Int(1))),
    #     "Loop runs at least two iterations for j < k",
    # )

    builder.assertions.append("\n; --- Dependency Logic Definitions ---")
    # New loop bounds for j and k
    j_lower_bound = GE(j, loop_start)
    j_upper_bound = LT(j, k)  # j < k
    k_lower_bound = GE(k, loop_start)
    k_upper_bound = LE(k, loop_end)

    builder.add_assertion(
        GE(loop_end, Plus(loop_start, Int(1))),
        "Loop runs at least two iterations for j < k",
    )

    # Combine all bounds
    loop_bound_formula = And(j_lower_bound, j_upper_bound, k_lower_bound, k_upper_bound)

    let_bindings, main_body_str = _build_dependency_logic_assertions_general(
        loop_node, j, k, builder, id_to_symbol_map
    )

    loop_bound_str = builder._serialize(loop_bound_formula)

    inner_forall_str = f"""(forall ({" ".join(universal_quantifier_vars)}) ; End of universal variables
    (=> {loop_bound_str}
    (let (
        {let_bindings}
        )
        ; Main formula
        (not {main_body_str})
    )
))"""

    # The DATA! symbols are now free variables, not existentially quantified.
    # The query asserts the inner forall directly.
    final_assertion_str = inner_forall_str

    builder.assertions.append(f"(assert {final_assertion_str})")

    smt_query = builder.build_query()
    if verbose:
        print(f"""
{smt_query}
""")
    return smt_query


def generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep(
    loop_node: Loop, extra_assertions: List[PysmtFormula] = None, verbose: bool = True
) -> str:
    """
    Generates an SMT-LIB query string to prove Data-Oblivious Full Independence (Φ_DOFI)
    for a given loop, with symbolic loop bounds explicitly universally quantified.

    This function is similar to `generate_smt_for_prove_exists_data_forall_iter_isindep`,
    but it explicitly includes any symbolic variables found in the loop's start and end
    bounds in the universal quantifier (`forall`) part of the SMT query. This means
    the solver will attempt to prove the property for *all possible integer values*
    of these symbolic loop bounds.

    A loop is considered Data-Oblivious Fully Independent (DOFI) if there exists *at least one*
    specific assignment of values to its symbolic data arrays (a "data configuration")
    such that *no* data dependency is guaranteed to exist between *any* pair of iterations
    (j and k, where j < k) within the loop's execution range.
    In simpler terms, a DOFI loop *can* be parallelized because there's at least one
    data scenario where no dependencies force sequential execution.

    The SMT query is constructed to find such a "parallelizing" data configuration.

    Interpretation of SMT Solver Results:
    - If the SMT solver returns `SAT` (Satisfiable), it means the query's assertion is true:
      it has found a data configuration for which *no* dependency exists between
      iterations `j` and `k` (where `j < k`) for all valid `j` and `k` AND for all
      possible values of the symbolic loop bounds.
      Therefore, the loop is **DOFI (Parallel)**.
    - If the SMT solver returns `UNSAT` (Unsatisfiable), it means the query's assertion is false:
      no such "parallelizing" data configuration exists. This implies that for *every*
      data configuration, there is at least one pair of iterations (j, k) with `j < k`
      that *does* have a dependency.
    """
    k = loop_node.loop_var  # Use the loop's internal iteration variable
    j = Symbol(f"{loop_node.loop_var.symbol_name()}_j", INT)  # New iteration variable j

    # Identify symbolic loop bound variables
    symbolic_loop_bounds = set()
    for free_var in _get_free_variables_recursive(loop_node.start):
        if free_var != k and free_var != j:
            symbolic_loop_bounds.add(free_var)
    for free_var in _get_free_variables_recursive(loop_node.end):
        if free_var != k and free_var != j:
            symbolic_loop_bounds.add(free_var)

    universal_quantifier_vars = [f"({k.symbol_name()} {k.get_type()})"]
    universal_quantifier_vars.append(f"({j.symbol_name()} {j.get_type()})")  # Add j
    for sym in symbolic_loop_bounds:
        universal_quantifier_vars.append(f"({sym.symbol_name()} {sym.get_type()})")

    builder = _StringSmtBuilder()

    # Declare universal quantifiers (k, j, and symbolic loop bounds)
    builder.declarations.add(k)
    builder.declarations.add(j)  # Add j
    for sym in symbolic_loop_bounds:
        builder.declarations.add(sym)

    id_to_symbol_map: Dict[int, PysmtSymbol] = {}
    all_data_nodes: Set[Data] = set()
    _collect_all_data_nodes(
        loop_node.builder.root_graph, all_data_nodes
    )  # Collect from the entire graph

    builder.assertions.append("; --- Data Definitions ---")
    for node in all_data_nodes:  # Iterate over all collected Data nodes
        sym = Symbol(f"DATA!{node.name}", INT)
        id_to_symbol_map[node.array_id] = sym
        # Explicitly add DATA! symbols to declarations
        builder.declarations.add(sym)

    existential_quantifier_vars = list(id_to_symbol_map.values())

    # NEW BLOCK: Add human-provided assertions
    if extra_assertions:
        builder.assertions.append("\n; --- Human-Provided Bounds/Assertions ---")
        for idx, assertion in enumerate(extra_assertions):
            builder.add_assertion(assertion, f"Human Assertion #{idx}")

    builder.assertions.append("\n; --- Loop Bounds ---")
    loop_start, loop_end = loop_node.start, loop_node.end

    builder.assertions.append("\n; --- Dependency Logic Definitions ---")
    # New loop bounds for j and k
    j_lower_bound = GE(j, loop_start)
    j_upper_bound = LT(j, k)  # j < k
    k_lower_bound = GE(k, loop_start)
    k_upper_bound = LE(k, loop_end)

    builder.add_assertion(
        GE(loop_end, Plus(loop_start, Int(1))),
        "Loop runs at least two iterations for j < k",
    )

    # Combine all bounds
    loop_bound_formula = And(j_lower_bound, j_upper_bound, k_lower_bound, k_upper_bound)

    let_bindings, main_body_str = _build_dependency_logic_assertions_general(
        loop_node, j, k, builder, id_to_symbol_map
    )

    loop_bound_str = builder._serialize(loop_bound_formula)

    inner_forall_str = f"""(forall ({" ".join(universal_quantifier_vars)}) ; End of universal variables
    (=> {loop_bound_str}
    (let (
        {let_bindings}
        )
        ; Main formula
        (not {main_body_str})
    )
))"""

    # The DATA! symbols are now free variables, not existentially quantified.
    # The query asserts the inner forall directly.
    final_assertion_str = inner_forall_str

    builder.assertions.append(f"(assert {final_assertion_str})")

    smt_query = builder.build_query()
    if verbose:
        print(f"""
{smt_query}
""")
    return smt_query


def generate_smt_for_prove_forall_data_forall_loop_bounds_iter_isindep(
    loop_node: Loop, extra_assertions: List[PysmtFormula] = None, verbose: bool = True
) -> str:
    """
    Generates an SMT-LIB query string to prove Data-Oblivious Full Independence (Φ_DOFI)
    for a given loop, with symbolic data arrays AND loop bounds explicitly universally quantified.

    This function is similar to `generate_smt_for_prove_exists_data_forall_loop_bounds_iter_isindep`,
    but it explicitly includes any symbolic variables found in the loop's data arrays
    (DATA! symbols) and loop bounds in the universal quantifier (`forall`) part of the SMT query.
    This means the solver will attempt to prove the property for *all possible integer values*
    of these symbolic data arrays and loop bounds.

    A loop is considered Data-Oblivious Fully Independent (DOFI) if for *all* possible
    assignments of values to its symbolic data arrays (a "data configuration") AND
    for *all* possible values of its symbolic loop bounds, *no* data dependency is
    guaranteed to exist between *any* pair of iterations (j and k, where j < k)
    within the loop's execution range.
    In simpler terms, a DOFI loop *can* be parallelized because under *any* data scenario
    and *any* loop bounds, no dependencies force sequential execution.

    The SMT query is constructed to prove this universal independence.

    Interpretation of SMT Solver Results:
    - If the SMT solver returns `SAT` (Satisfiable), it means the query's assertion is true:
      for *all* data configurations and *all* loop bounds, *no* dependency exists between
      iterations `j` and `k` (where `j < k`) for all valid `j` and `k`.
      Therefore, the loop is **DOFI (Parallel)**.
    - If the SMT solver returns `UNSAT` (Unsatisfiable), it means the query's assertion is false:
      there exists *at least one* data configuration OR *at least one* set of loop bounds
      for which there is at least one pair of iterations (j, k) with `j < k`
      that *does* have a dependency.
      Therefore, the loop is **not DOFI (Sequential)**.

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
    j = Symbol(f"{loop_node.loop_var.symbol_name()}_j", INT)  # New iteration variable j

    # Identify symbolic loop bound variables
    symbolic_loop_bounds = set()
    for free_var in _get_free_variables_recursive(loop_node.start):
        if free_var != k and free_var != j:
            symbolic_loop_bounds.add(free_var)
    for free_var in _get_free_variables_recursive(loop_node.end):
        if free_var != k and free_var != j:
            symbolic_loop_bounds.add(free_var)

    universal_quantifier_vars = [f"({k.symbol_name()} {k.get_type()})"]
    universal_quantifier_vars.append(f"({j.symbol_name()} {j.get_type()})")  # Add j
    for sym in symbolic_loop_bounds:
        universal_quantifier_vars.append(f"({sym.symbol_name()} {sym.get_type()})")

    builder = _StringSmtBuilder()

    # Declare universal quantifiers (k, j, and symbolic loop bounds)
    builder.declarations.add(k)
    builder.declarations.add(j)  # Add j
    for sym in symbolic_loop_bounds:
        builder.declarations.add(sym)

    id_to_symbol_map: Dict[int, PysmtSymbol] = {}
    all_data_nodes: Set[Data] = set()
    _collect_all_data_nodes(
        loop_node.builder.root_graph, all_data_nodes
    )  # Collect from the entire graph

    builder.assertions.append("; --- Data Definitions ---")
    forall_data_quantifier_vars = []  # NEW: Collect data symbols for universal quantification
    for node in all_data_nodes:  # Iterate over all collected Data nodes
        sym = Symbol(f"DATA!{node.name}", INT)
        id_to_symbol_map[node.array_id] = sym
        # Explicitly add DATA! symbols to declarations
        builder.declarations.add(sym)
        forall_data_quantifier_vars.append(
            f"({sym.symbol_name()} {sym.get_type()})"
        )  # NEW

    # existential_quantifier_vars = list(id_to_symbol_map.values()) # REMOVE/COMMENT OUT

    # NEW BLOCK: Add human-provided assertions
    if extra_assertions:
        builder.assertions.append("\n; --- Human-Provided Bounds/Assertions ---")
        for idx, assertion in enumerate(extra_assertions):
            builder.add_assertion(assertion, f"Human Assertion #{idx}")

    builder.assertions.append("\n; --- Loop Bounds ---")
    loop_start, loop_end = loop_node.start, loop_node.end

    builder.assertions.append("\n; --- Dependency Logic Definitions ---")
    # New loop bounds for j and k
    j_lower_bound = GE(j, loop_start)
    j_upper_bound = LT(j, k)  # j < k
    k_lower_bound = GE(k, loop_start)
    k_upper_bound = LE(k, loop_end)

    builder.add_assertion(
        GE(loop_end, Plus(loop_start, Int(1))),
        "Loop runs at least two iterations for j < k",
    )

    # Combine all bounds
    loop_bound_formula = And(j_lower_bound, j_upper_bound, k_lower_bound, k_upper_bound)

    let_bindings, main_body_str = _build_dependency_logic_assertions_general(
        loop_node, j, k, builder, id_to_symbol_map
    )

    loop_bound_str = builder._serialize(loop_bound_formula)

    inner_forall_str = f"""(forall ({" ".join(universal_quantifier_vars)}) ; End of universal variables
    (=> {loop_bound_str}
    (let (
        {let_bindings}
        )
        ; Main formula
        (not {main_body_str})
    )
))"""

    # NEW: Wrap the inner forall with another forall for data variables
    final_assertion_str = f"""(forall ({" ".join(forall_data_quantifier_vars)})
    {inner_forall_str}
)"""

    builder.assertions.append(f"(assert {final_assertion_str})")

    smt_query = builder.build_query()
    if verbose:
        print(f"""
{smt_query}
""")
    return smt_query
