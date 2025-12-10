from __future__ import annotations

import dace
import sympy as sp
from dace.sdfg import SDFG
from dace.sdfg.nodes import AccessNode, Tasklet, MapEntry, MapExit, NestedSDFG
from dace.sdfg.state import LoopRegion, SDFGState, ConditionalBlock
from dace.sdfg.utils import dfs_topological_sort
from dace.transformation.passes.analysis.loop_analysis import (
    get_loop_end,
    get_init_assignment,
)

# Define keywords used in P3G to avoid clashes with SDFG symbol names
P3G_KEYWORDS = {
    "FORALL",
    "EXISTS",
    "AND",
    "OR",
    "NOT",
    "SELECT",
    "INT_TYPE",
    "DECL",
    "SYM",
    "VAR",
    "OUT",
    "FOR",
    "TO",
    "IF",
    "ELSE",
    "OP",
    "GE",
    "LE",
    "ARROW",
    "EQ",
    "GT",
    "LT",
    "PIPE",
    "COLON",
    "LPAREN",
    "RPAREN",
    "LBRACKET",
    "RBRACKET",
    "PLUS",
    "MINUS",
    "TIMES",
    "IDIV",
    "MOD",
    "DIVIDE",
    "COMMA",
    "DOT",
    "BANG",
}


class SDFGToPseudocodeConverter:
    """
    Translates a DaCe SDFG into a P3G pseudocode string.
    """

    def __init__(self, sdfg: SDFG):
        self.sdfg = sdfg
        self.pseudocode_lines: list[str] = []
        self._indent_level = 0
        self._next_stmt_id = 1
        self._current_scope_stmt_name: str | None = None

        # Track declared symbols, arrays, and loop variables
        self._declared_arrays: set[str] = set()
        self._declared_symbols: set[str] = set()
        self._declared_loop_vars: set[str] = set()

        # Dataflow tracking
        # Maps array_name to the name of the statement that last wrote to it in the current scope
        self._array_state: dict[str, str] = {}
        # Stack to manage scope for dataflow (e.g., entering/exiting loops, branches)
        self._current_array_state_stack: list[str] = ["."]

        # Track processed CFG nodes to avoid redundant processing in conditional branches
        self._processed_cfg_nodes: set[dace.sdfg.nodes.Node] = set()
        self._processed_dataflow_nodes: set[dace.sdfg.nodes.Node] = set()

    def _indent(self):
        return "    " * self._indent_level

    def _add_line(self, line: str):
        self.pseudocode_lines.append(self._indent() + line)

    def _get_next_stmt_name(self, prefix: str = "S") -> str:
        name = f"{prefix}{self._next_stmt_id}"
        self._next_stmt_id += 1
        return name

    def _convert_sympy_to_pseudocode_expr(
        self, expr: sp.Expr, wrap_if_complex: bool = False
    ) -> str:
        """
        Converts a SymPy expression to its pseudocode string representation.
        Handles basic arithmetic, symbols, and literals.
        If wrap_if_complex is True, adds parentheses if the expression is not a simple atom.
        """
        expr_str: str
        if isinstance(expr, sp.Integer):
            expr_str = str(expr)
        elif expr == sp.true:
            expr_str = "true"
        elif expr == sp.false:
            expr_str = "false"
        elif isinstance(expr, sp.Tuple):
            raise NotImplementedError(
                f"Multi-element SymPy expression (Tuple: {expr}) not directly "
                "supported as a single argument in PCode. "
                "Requires specific handling for conversion."
            )
        elif isinstance(expr, sp.Symbol):
            expr_str = str(expr)
        elif isinstance(expr, sp.Add):
            expr_str = " + ".join(
                self._convert_sympy_to_pseudocode_expr(arg, wrap_if_complex=True)
                for arg in expr.args
            )
        elif isinstance(expr, sp.Mul):
            factors = []
            for arg in expr.args:
                if isinstance(
                    arg, (sp.Add, sp.Mul, sp.Pow)
                ):  # Apply parentheses for nested arithmetic
                    factors.append(
                        f"({self._convert_sympy_to_pseudocode_expr(arg, wrap_if_complex=True)})"
                    )
                else:
                    factors.append(
                        self._convert_sympy_to_pseudocode_expr(
                            arg, wrap_if_complex=False
                        )
                    )
            expr_str = " * ".join(factors)
        elif isinstance(expr, sp.Pow):
            base = self._convert_sympy_to_pseudocode_expr(
                expr.base, wrap_if_complex=True
            )
            exp = self._convert_sympy_to_pseudocode_expr(expr.exp, wrap_if_complex=True)
            if expr.exp == -1:
                expr_str = f"1 / {base}"
            else:
                expr_str = f"{base}**{exp}"
        elif isinstance(expr, sp.Equality):
            expr_str = f"{self._convert_sympy_to_pseudocode_expr(expr.lhs, wrap_if_complex=True)} = {self._convert_sympy_to_pseudocode_expr(expr.rhs, wrap_if_complex=True)}"
        elif isinstance(expr, sp.GreaterThan):
            expr_str = f"{self._convert_sympy_to_pseudocode_expr(expr.lhs, wrap_if_complex=True)} >= {self._convert_sympy_to_pseudocode_expr(expr.rhs, wrap_if_complex=True)}"
        elif isinstance(expr, sp.LessThan):
            expr_str = f"{self._convert_sympy_to_pseudocode_expr(expr.lhs, wrap_if_complex=True)} <= {self._convert_sympy_to_pseudocode_expr(expr.rhs, wrap_if_complex=True)}"
        elif isinstance(expr, sp.StrictGreaterThan):
            expr_str = f"{self._convert_sympy_to_pseudocode_expr(expr.lhs, wrap_if_complex=True)} > {self._convert_sympy_to_pseudocode_expr(expr.rhs, wrap_if_complex=True)}"
        elif isinstance(expr, sp.StrictLessThan):
            expr_str = f"{self._convert_sympy_to_pseudocode_expr(expr.lhs, wrap_if_complex=True)} < {self._convert_sympy_to_pseudocode_expr(expr.rhs, wrap_if_complex=True)}"
        elif isinstance(expr, sp.Indexed):
            base = str(expr.base)
            indices = ", ".join(
                self._convert_sympy_to_pseudocode_expr(idx, wrap_if_complex=False)
                for idx in expr.indices
            )
            expr_str = f"{base}[{indices}]"

        # Basic support for some functions (e.g., floor, sqrt used in examples)
        elif isinstance(expr, sp.Function):
            if expr.func == sp.Min:
                args_str = ", ".join(
                    self._convert_sympy_to_pseudocode_expr(arg, wrap_if_complex=True)
                    for arg in expr.args
                )
                expr_str = f"min({args_str})"
            elif expr.func == sp.Max:
                args_str = ", ".join(
                    self._convert_sympy_to_pseudocode_expr(arg, wrap_if_complex=True)
                    for arg in expr.args
                )
                expr_str = f"max({args_str})"
            elif expr.func == sp.Floor:
                args_str = ", ".join(
                    self._convert_sympy_to_pseudocode_expr(arg, wrap_if_complex=True)
                    for arg in expr.args
                )
                expr_str = f"floor({args_str})"
            else:
                raise NotImplementedError(
                    f"Unsupported SymPy function in expression: {expr.func}"
                )
        else:
            # Fallback for unhandled types
            expr_str = str(expr)

        if wrap_if_complex and not isinstance(
            expr, (sp.Integer, sp.Symbol, sp.Indexed)
        ):
            return f"({expr_str})"
        return expr_str

    def _get_read_accesses_from_expression(
        self, sympy_expr: sp.Expr
    ) -> list[tuple[str, str]]:
        """
        Recursively extracts read accesses (array name and subset string) from a SymPy expression.
        """
        accesses = []
        if isinstance(sympy_expr, sp.Indexed):
            base_name = str(sympy_expr.base)
            indices_str = ", ".join(
                self._convert_sympy_to_pseudocode_expr(idx, wrap_if_complex=True)
                for idx in sympy_expr.indices
            )
            accesses.append((base_name, indices_str))
        for arg in sympy_expr.args:
            accesses.extend(self._get_read_accesses_from_expression(arg))
        return accesses

    def _parse_code_block_to_sympy(
        self, code_block: dace.properties.CodeBlock
    ) -> sp.Expr:
        """Converts a dace.properties.CodeBlock into a sympy.Expr."""
        code_str = code_block.as_string
        try:
            return sp.sympify(code_str)
        except TypeError as e:
            if "'Symbol' object is not subscriptable" in str(e):
                # SymPy struggles with direct array indexing.
                # Provide context for declared arrays as IndexedBase.
                sympy_locals = {
                    name: sp.IndexedBase(name) for name in self._declared_arrays
                }
                # Also include loop variables and symbols for completeness
                sympy_locals.update(
                    {name: sp.Symbol(name) for name in self._declared_loop_vars}
                )
                sympy_locals.update(
                    {name: sp.Symbol(name) for name in self._declared_symbols}
                )
                try:
                    return sp.sympify(code_str, locals=sympy_locals)
                except (sp.SympifyError, TypeError) as e2:
                    print(
                        f"ERROR: Failed to sympify with IndexedBase context '{code_str}': {e2}. "
                        "Re-raising for explicit handling."
                    )
                    raise e2  # Re-raise the exception
            else:
                print(
                    f"ERROR: Could not directly sympify '{code_str}': {e}. "
                    "Re-raising for explicit handling."
                )
                raise e  # Re-raise the exception
        except sp.SympifyError as e:
            print(
                f"ERROR: Could not directly sympify '{code_str}': {e}. "
                "Re-raising for explicit handling."
            )
            raise e  # Re-raise the exception

    def _convert_sympy_boolean_to_pseudocode(self, expr: sp.Expr) -> str:
        """
        Converts a SymPy boolean expression to its pseudocode string representation.
        Handles logical operators.
        """
        if isinstance(expr, sp.And):
            return " and ".join(
                self._convert_sympy_boolean_to_pseudocode(arg) for arg in expr.args
            )
        elif isinstance(expr, sp.Or):
            return " or ".join(
                self._convert_sympy_boolean_to_pseudocode(arg) for arg in expr.args
            )
        elif isinstance(expr, sp.Not):
            # If the argument is a comparison, wrap it for clarity.
            arg_str = self._convert_sympy_boolean_to_pseudocode(expr.args[0])
            if isinstance(
                expr.args[0],
                (
                    sp.Equality,
                    sp.GreaterThan,
                    sp.LessThan,
                    sp.StrictGreaterThan,
                    sp.StrictLessThan,
                ),
            ):
                return f"not ({arg_str})"
            return f"not {arg_str}"
        elif isinstance(expr, sp.Equality):
            return f"{self._convert_sympy_to_pseudocode_expr(expr.lhs, wrap_if_complex=True)} == {self._convert_sympy_to_pseudocode_expr(expr.rhs, wrap_if_complex=True)}"
        elif isinstance(expr, sp.GreaterThan):
            return f"{self._convert_sympy_to_pseudocode_expr(expr.lhs, wrap_if_complex=True)} >= {self._convert_sympy_to_pseudocode_expr(expr.rhs, wrap_if_complex=True)}"
        elif isinstance(expr, sp.LessThan):
            return f"{self._convert_sympy_to_pseudocode_expr(expr.lhs, wrap_if_complex=True)} <= {self._convert_sympy_to_pseudocode_expr(expr.rhs, wrap_if_complex=True)}"
        elif isinstance(expr, sp.StrictGreaterThan):
            return f"{self._convert_sympy_to_pseudocode_expr(expr.lhs, wrap_if_complex=True)} > {self._convert_sympy_to_pseudocode_expr(expr.rhs, wrap_if_complex=True)}"
        elif isinstance(expr, sp.StrictLessThan):
            return f"{self._convert_sympy_to_pseudocode_expr(expr.lhs, wrap_if_complex=True)} < {self._convert_sympy_to_pseudocode_expr(expr.rhs, wrap_if_complex=True)}"
        else:
            return self._convert_sympy_to_pseudocode_expr(expr, wrap_if_complex=True)

    def _convert_memlet_subset_to_pseudocode(self, subset) -> str:
        """
        Converts a DaCe Memlet's subset to pseudocode range format.
        Assumes single dimension for simplicity for now, or takes first range.
        """
        if not subset.ranges:
            return ""  # Empty subset

        ranges_str = []
        for r in subset.ranges:
            start = self._convert_sympy_to_pseudocode_expr(r[0], wrap_if_complex=True)
            end = self._convert_sympy_to_pseudocode_expr(r[1], wrap_if_complex=True)
            # For a single element, start == end, so just print start
            if start == end:
                ranges_str.append(start)
            else:
                ranges_str.append(f"{start}:{end}")
        return ", ".join(ranges_str)

    def _convert_accesses_to_pseudocode(
        self, access_list: list[tuple[str, str]]
    ) -> str:
        """
        Converts a list of (array_name, subset_str) tuples into the pseudocode
        access format, e.g., "A[i], B[0:N]".
        """
        if not access_list:
            return ""
        return ", ".join([f"{name}[{subset}]" for name, subset in access_list])

    def _convert_node(self, node: dace.sdfg.nodes.Node, state: SDFGState):
        """
        Generic dispatcher for converting SDFG nodes to pseudocode statements.
        """
        if node in self._processed_dataflow_nodes:
            return
        self._processed_dataflow_nodes.add(node)

        if isinstance(node, Tasklet):
            self._convert_tasklet(node, state)
        elif isinstance(node, AccessNode):
            # AccessNodes often don't translate to explicit statements unless it's a transient read/write
            # For now, we handle them implicitly through memlets of other nodes.
            pass
        elif isinstance(node, MapEntry):
            self._convert_map_entry(node, state)
        elif isinstance(node, NestedSDFG):
            self._convert_nested_sdfg(node, state)
        else:
            raise NotImplementedError(
                f"Conversion for node type {type(node)} not yet implemented."
            )

    def _convert_tasklet(self, tasklet: Tasklet, state: SDFGState):
        # Determine source states for reads and update array_state for writes
        source_states: dict[str, str] = {}  # {array_name: producing_stmt_name}
        current_read_accesses: list[tuple[str, str]] = []
        current_write_accesses: list[tuple[str, str]] = []

        # Collect explicit reads
        for edge in state.in_edges(tasklet):
            if edge.data.data:
                array_name = edge.data.data
                subset_str = self._convert_memlet_subset_to_pseudocode(edge.data.subset)
                current_read_accesses.append((array_name, subset_str))
                producer = self._array_state.get(array_name, ".")
                source_states[array_name] = producer

        # Collect writes (and also implicitly add them to reads for SSA)
        for edge in state.out_edges(tasklet):
            if edge.data.data:
                array_name = edge.data.data
                subset_str = self._convert_memlet_subset_to_pseudocode(edge.data.subset)
                current_write_accesses.append((array_name, subset_str))
                # If an array is written, it's also implicitly read from its previous version
                if (array_name, subset_str) not in current_read_accesses:
                    current_read_accesses.append((array_name, subset_str))
                producer = self._array_state.get(array_name, ".")
                source_states[array_name] = producer

        read_str = self._convert_accesses_to_pseudocode(current_read_accesses)
        write_str = self._convert_accesses_to_pseudocode(current_write_accesses)

        stmt_name = self._get_next_stmt_name("T")

        # Construct source_states string for pseudocode
        unique_source_stmts = sorted(list(set(source_states.values())))
        # Filter out "." which represents the initial state and should be indicated by "()"
        filtered_source_stmts = [s for s in unique_source_stmts if s != "."]

        if not filtered_source_stmts:
            dataflow_prefix = "()."  # Explicit empty source states
        else:
            source_states_str = ", ".join(filtered_source_stmts)
            dataflow_prefix = f"({source_states_str})."

        # The syntax for op is: (READS => WRITES) (<source_states>).<stmt_name>| op(<description>)
        self._add_line(
            f"({read_str} => {write_str}) {dataflow_prefix}{stmt_name}| op({tasklet.label})"
        )

        # After the statement, update the _array_state for all arrays written by this tasklet
        for array_name, _ in current_write_accesses:
            self._array_state[array_name] = stmt_name

        self._current_scope_stmt_name = stmt_name

    def _convert_map_entry(self, map_entry: MapEntry, state: SDFGState):
        map_ = map_entry.map
        if len(map_.params) > 1:
            raise NotImplementedError(
                "Multi-dimensional maps not yet supported for pseudocode conversion."
            )

        param = map_.params[0]
        self._declared_loop_vars.add(param)

        map_range = map_.range[0]  # Assuming single range
        start_expr = self._convert_sympy_to_pseudocode_expr(
            map_range[0], wrap_if_complex=True
        )
        end_expr = self._convert_sympy_to_pseudocode_expr(
            map_range[1], wrap_if_complex=True
        )
        reads_map_boundary = []
        writes_map_boundary = []

        # Collect reads
        source_states: dict[str, str] = {}
        for edge in state.in_edges(map_entry):
            if edge.data.data:
                array_name = edge.data.data
                # subset_str = self._convert_memlet_subset_to_pseudocode(edge.data.subset)
                reads_map_boundary.append((array_name, "0"))
                source_states[array_name] = self._array_state.get(array_name, ".")

        map_exit = state.exit_node(map_entry)
        for edge in state.out_edges(map_exit):
            if edge.data.data:
                array_name = edge.data.data
                # subset_str = self._convert_memlet_subset_to_pseudocode(edge.data.subset)
                writes_map_boundary.append((array_name, "0"))
                # Map writes also implicitly read from their previous version for SSA
                if (array_name, "0") not in reads_map_boundary:
                    reads_map_boundary.append((array_name, "0"))
                source_states[array_name] = self._array_state.get(array_name, ".")

        read_str = self._convert_accesses_to_pseudocode(reads_map_boundary)
        write_str = self._convert_accesses_to_pseudocode(writes_map_boundary)

        stmt_name = self._get_next_stmt_name("M")

        # Construct source_states string for pseudocode
        unique_source_stmts = sorted(list(set(source_states.values())))
        # Filter out "." which represents the initial state and should be indicated by "()"
        filtered_source_stmts = [s for s in unique_source_stmts if s != "."]

        if not filtered_source_stmts:
            dataflow_prefix = "()."  # Explicit empty source states
        else:
            source_states_str = ", ".join(filtered_source_stmts)
            dataflow_prefix = f"({source_states_str})."

        self._add_line(
            f"({read_str} => {write_str}) {dataflow_prefix}{stmt_name}| map {param} = {start_expr} to {end_expr}:"
        )

        self._indent_level += 1

        # Push current array state and scope statement onto stack
        self._current_array_state_stack.append(self._current_scope_stmt_name)
        old_array_state = self._array_state.copy()

        # Initialize _array_state for the new scope with inputs to the map
        self._array_state = {k: v for k, v in source_states.items()}

        self._current_scope_stmt_name = (
            stmt_name  # The map itself is the parent for its body
        )

        # Recursively convert nodes inside the map
        scope_subgraph = state.scope_subgraph(map_entry)
        for node in dfs_topological_sort(scope_subgraph):
            if node == map_entry:
                continue
            # Only process direct children of this map to preserve hierarchy
            if state.entry_node(node) != map_entry:
                continue
            if isinstance(
                node, (dace.sdfg.nodes.MapExit, AccessNode)
            ):  # Avoid re-processing MapExit or raw AccessNodes
                continue
            self._convert_node(node, state)

        self._indent_level -= 1

        # Pop scope and restore array state.
        # For arrays written by the map, their state in the outer scope is now this map's statement.
        self._current_scope_stmt_name = self._current_array_state_stack.pop()
        for array_name, _ in writes_map_boundary:
            old_array_state[array_name] = stmt_name
        self._array_state = old_array_state

    def convert_body(self):
        """
        Converts the body of the SDFG (CFG nodes) to pseudocode without declarations.
        """
        for node in dfs_topological_sort(self.sdfg):
            self._convert_cfg_node(node, self.sdfg)

    def _convert_nested_sdfg(self, nested_sdfg_node: NestedSDFG, state: SDFGState):
        reads = []
        writes = []

        source_states: dict[str, str] = {}

        # Collect reads from incoming memlets
        for k, v in nested_sdfg_node.in_connectors.items():
            for edge in state.in_edges(nested_sdfg_node):
                if edge.dst_conn == k and edge.data.data:
                    array_name = edge.data.data
                    subset_str = self._convert_memlet_subset_to_pseudocode(
                        edge.data.subset
                    )
                    reads.append((array_name, subset_str))

                    producer = self._array_state.get(array_name, ".")
                    source_states[array_name] = producer

        # Collect writes from outgoing memlets (and also explicitly add them to reads for SSA)
        for k, v in nested_sdfg_node.out_connectors.items():
            for edge in state.out_edges(nested_sdfg_node):
                if edge.src_conn == k and edge.data.data:
                    array_name = edge.data.data
                    subset_str = self._convert_memlet_subset_to_pseudocode(
                        edge.data.subset
                    )
                    writes.append((array_name, subset_str))

                    # If an array is written, it's also implicitly read from its previous version
                    if (array_name, subset_str) not in reads:
                        reads.append((array_name, subset_str))

                    producer = self._array_state.get(array_name, ".")
                    source_states[array_name] = producer

        read_str = self._convert_accesses_to_pseudocode(reads)
        write_str = self._convert_accesses_to_pseudocode(writes)

        stmt_name = self._get_next_stmt_name("NS")  # Define stmt_name here

        # Construct source_states string for pseudocode
        unique_source_stmts = sorted(list(set(source_states.values())))
        # Filter out "." which represents the initial state and should be indicated by "()"
        filtered_source_stmts = [s for s in unique_source_stmts if s != "."]

        if not filtered_source_stmts:
            dataflow_prefix = "()."  # Explicit empty source states
        else:
            source_states_str = ", ".join(filtered_source_stmts)
            dataflow_prefix = f"({source_states_str})."

        # Instead of opaque op, try to inline the nested SDFG

        # self._add_line(
        #     f"({read_str} => {write_str}) {dataflow_prefix}{stmt_name}| op(NestedSDFG: {nested_sdfg_node.label})"
        # )

        # Recursively convert the nested SDFG body
        nested_converter = SDFGToPseudocodeConverter(nested_sdfg_node.sdfg)
        # Propagate indentation level
        nested_converter._indent_level = self._indent_level
        # Propagate array state (basic heuristic, might not map perfectly without explicit symbol mapping logic)
        # nested_converter._array_state = self._array_state.copy() # Too risky without mapping

        # We need to collect declarations from nested SDFG if we haven't already
        # But convert_body doesn't print them. They should have been collected by the top-level
        # _collect_all_declarations_and_outputs if traversed correctly.

        # Run conversion of body
        nested_converter.convert_body()

        # Append lines to current lines
        self.pseudocode_lines.extend(nested_converter.pseudocode_lines)

        # Update array state for all arrays written by this NestedSDFG
        # This assumes the nested SDFG execution is atomic regarding these writes in the current scope
        for array_name, _ in writes:
            self._array_state[array_name] = stmt_name

        self._current_scope_stmt_name = stmt_name

    def _convert_cfg_node(self, node, parent_cfg_node):
        """
        Converts control flow graph (CFG) nodes like SDFGState, LoopRegion, ConditionalBlock.
        `parent_cfg_node` is the SDFG or LoopRegion that contains `node`.
        """
        if node in self._processed_cfg_nodes:
            return

        if isinstance(node, SDFGState):
            # Try to process as a conditional state first (if it's the entry of a conditional branch)
            processed_by_conditional = self._process_conditional_state(
                node, parent_cfg_node
            )
            if processed_by_conditional:
                self._processed_cfg_nodes.update(processed_by_conditional)
                return  # This state and its branches have been processed

            # If not processed as a conditional, mark the state itself as processed and convert its dataflow nodes
            self._processed_cfg_nodes.add(node)
            dataflow_nodes = list(dfs_topological_sort(node))
            if not dataflow_nodes:
                # If the SDFGState is empty, add a NOOP operation to maintain structure
                self._add_line(f"( => ) noop | op(NOOP_state_{node.label})")
            else:
                # Recursively convert all dataflow nodes within the state
                for dnode in dataflow_nodes:
                    # Only process top-level nodes in the state (not inside any map)
                    if node.entry_node(dnode) is not None:
                        continue
                    # Skip MapExit nodes as they are handled by MapEntry, and raw AccessNodes
                    if isinstance(dnode, (dace.sdfg.nodes.MapExit, AccessNode)):
                        continue
                    self._convert_node(
                        dnode, node
                    )  # Pass the SDFGState 'node' as context for dataflow nodes
        elif isinstance(node, LoopRegion):
            self._processed_cfg_nodes.add(node)
            self._convert_loop_region(node, parent_cfg_node)
        elif isinstance(node, ConditionalBlock):
            self._processed_cfg_nodes.add(node)
            self._convert_conditional_block(node, parent_cfg_node)
        else:
            raise NotImplementedError(
                f"Conversion for CFG node type {type(node)} not yet implemented."
            )

    def _convert_sdfg_state(self, state: SDFGState, parent_cfg_node):
        # This method now only processes dataflow nodes within a simple SDFGState.
        # Conditional state detection and processing is handled in _convert_cfg_node.
        for node in dfs_topological_sort(state):
            # Skip MapExit nodes as they are handled by MapEntry, and raw AccessNodes
            if isinstance(node, (dace.sdfg.nodes.MapExit, AccessNode)):
                continue
            self._convert_node(node, state)

    def _collect_region_accesses(self, region):
        reads = set()
        writes = set()

        def process_state(state):
            for node in state.nodes():
                if isinstance(node, AccessNode):
                    if state.out_degree(node) > 0:
                        reads.add(node.data)
                    if state.in_degree(node) > 0:
                        writes.add(node.data)

        nodes_to_process = []
        if isinstance(region, (LoopRegion, dace.sdfg.SDFG)):
            nodes_to_process = region.nodes()
        elif isinstance(region, ConditionalBlock):
            for _, body in region.branches:
                # body is a ControlFlowRegion (like LoopRegion/SDFG structure)
                nodes_to_process.append(body)
        elif isinstance(region, SDFGState):
            process_state(region)
            return sorted(list(reads)), sorted(list(writes))

        for node in nodes_to_process:
            if isinstance(node, SDFGState):
                process_state(node)
            elif isinstance(node, (LoopRegion, ConditionalBlock)):
                r, w = self._collect_region_accesses(node)
                reads.update(r)
                writes.update(w)
            elif isinstance(
                node, dace.sdfg.state.ControlFlowRegion
            ):  # Generic catch for nested regions in branches
                r, w = self._collect_region_accesses(node)
                reads.update(r)
                writes.update(w)

        return sorted(list(reads)), sorted(list(writes))

    def _convert_loop_region(self, loop_region: LoopRegion, parent_cfg_node):
        loop_var_str = loop_region.loop_variable
        self._declared_loop_vars.add(loop_var_str)

        start_expr = self._convert_sympy_to_pseudocode_expr(
            get_init_assignment(loop_region), wrap_if_complex=True
        )
        end_expr = self._convert_sympy_to_pseudocode_expr(
            get_loop_end(loop_region), wrap_if_complex=True
        )

        r_vars, w_vars = self._collect_region_accesses(loop_region)
        reads_loop_boundary = [(r, "0") for r in r_vars]
        writes_loop_boundary = [(w, "0") for w in w_vars]

        read_str = self._convert_accesses_to_pseudocode(reads_loop_boundary)
        write_str = self._convert_accesses_to_pseudocode(writes_loop_boundary)

        # Determine source states for arrays that are read into the loop region from outside
        source_states: dict[str, str] = {}
        for array_name in self._array_state:
            source_states[array_name] = self._array_state[array_name]

        stmt_name = self._get_next_stmt_name("L")

        # Construct source_states string for pseudocode
        unique_source_stmts = sorted(list(set(source_states.values())))
        # Filter out "." which represents the initial state and should be indicated by "()"
        filtered_source_stmts = [s for s in unique_source_stmts if s != "."]

        if not filtered_source_stmts:
            dataflow_prefix = "()."  # Explicit empty source states
        else:
            source_states_str = ", ".join(filtered_source_stmts)
            dataflow_prefix = f"({source_states_str})."

        self._add_line(
            f"({read_str} => {write_str}) {dataflow_prefix}{stmt_name}| for {loop_var_str} = {start_expr} to {end_expr}:"
        )

        self._indent_level += 1

        # Push current array state and scope statement onto stack
        self._current_array_state_stack.append(self._current_scope_stmt_name)
        old_array_state = self._array_state.copy()

        # Initialize _array_state for the new scope with inputs to the loop
        self._array_state = {k: v for k, v in source_states.items()}

        self._current_scope_stmt_name = (
            stmt_name  # The loop itself is the parent for its body
        )

        # Recursively convert CFG nodes inside the loop
        for node in dfs_topological_sort(loop_region):
            self._convert_cfg_node(node, loop_region)

        self._indent_level -= 1

        # Pop scope and restore array state.
        # For arrays written by the loop, their state in the outer scope is now this loop's statement.
        self._current_scope_stmt_name = self._current_array_state_stack.pop()
        # For arrays written within the loop, update their state in the outer scope.
        # This requires identifying what was written. For now, assuming any array written in body
        # is updated by this statement.
        for array_name, producer_stmt in self._array_state.items():
            if producer_stmt != old_array_state.get(
                array_name
            ):  # If it was written *within* this loop
                old_array_state[array_name] = stmt_name
        self._array_state = old_array_state

    def _convert_conditional_block(self, cond_block: ConditionalBlock, parent_cfg_node):
        # Determine source states for arrays that are read into the conditional block from outside
        source_states: dict[str, str] = {}
        for array_name in self._array_state:
            source_states[array_name] = self._array_state[array_name]

        r_vars, w_vars = self._collect_region_accesses(cond_block)
        reads_cond_boundary = [(r, "0") for r in r_vars]
        writes_cond_boundary = [(w, "0") for w in w_vars]

        read_str = self._convert_accesses_to_pseudocode(reads_cond_boundary)
        write_str = self._convert_accesses_to_pseudocode(writes_cond_boundary)

        stmt_name = self._get_next_stmt_name("B")

        # Construct source_states string for pseudocode
        unique_source_stmts = sorted(list(set(source_states.values())))
        # Filter out "." which represents the initial state and should be indicated by "()"
        filtered_source_stmts = [s for s in unique_source_stmts if s != "."]

        if not filtered_source_stmts:
            dataflow_prefix = "()."  # Explicit empty source states
        else:
            source_states_str = ", ".join(filtered_source_stmts)
            dataflow_prefix = f"({source_states_str})."

        # Store initial _array_state to restore for each branch
        initial_array_state_for_branches = self._array_state.copy()

        # Keep track of _array_state after each branch to merge them later
        array_states_after_branches: list[dict[str, str]] = []

        self._current_array_state_stack.append(self._current_scope_stmt_name)
        self._current_scope_stmt_name = (
            stmt_name  # The branch itself is the parent for its body
        )

        else_handled = False
        num_branches = len(cond_block.branches)
        for i, (dace_cond_codeblock, branch_cfg) in enumerate(cond_block.branches):
            # Restore _array_state to the state before the conditional block for each branch
            self._array_state = initial_array_state_for_branches.copy()

            # Determine if this is an 'else' branch
            is_else_branch = False
            if (
                dace_cond_codeblock is None or dace_cond_codeblock.code == "1"
            ):  # Handle implicit else or explicit '1' condition
                is_else_branch = True
            elif num_branches > 1 and i == num_branches - 1 and not else_handled:
                # Heuristic: If it's the last branch in a multi-branch conditional,
                # and no 'else' has been handled yet, treat it as the implicit 'else'.
                is_else_branch = True

            if is_else_branch:  # This branch is the 'else'
                self._add_line(f"else:")
                else_handled = True
            else:
                if else_handled:
                    raise ValueError("'else' branch must be last in ConditionalBlock.")

                # Parse the CodeBlock condition to a SymPy expression
                sympy_cond_expr = self._parse_code_block_to_sympy(dace_cond_codeblock)
                cond_str = self._convert_sympy_boolean_to_pseudocode(sympy_cond_expr)

                if i == 0:  # First branch is 'if'
                    self._add_line(
                        f"({read_str} => {write_str}) {dataflow_prefix}{stmt_name}| if {cond_str}:"
                    )
                else:  # Subsequent branches are 'else if'
                    self._add_line(f"else if {cond_str}:")

            self._indent_level += 1
            # Recursively convert CFG nodes inside the branch
            for node in dfs_topological_sort(branch_cfg):
                self._convert_cfg_node(node, branch_cfg)  # Pass the branch_cfg
            self._indent_level -= 1

            array_states_after_branches.append(self._array_state.copy())

        # Merge _array_state after all branches
        merged_array_state = initial_array_state_for_branches.copy()
        modified_arrays_in_any_branch = set()

        for branch_state in array_states_after_branches:
            for array_name, producer_stmt in branch_state.items():
                # If an array was modified in this branch (its producer is not the initial one)
                if initial_array_state_for_branches.get(array_name) != producer_stmt:
                    modified_arrays_in_any_branch.add(array_name)

        for array_name in modified_arrays_in_any_branch:
            merged_array_state[array_name] = (
                stmt_name  # The conditional block is the new producer
            )

        self._array_state = merged_array_state
        self._current_scope_stmt_name = self._current_array_state_stack.pop()

    def _process_conditional_state(
        self, state: SDFGState, parent_sdfg: SDFG
    ) -> set[SDFGState]:
        """
        Processes a state that is the source of conditional InterstateEdges.
        Generates if/else pseudocode and recursively converts branched states.
        Returns the set of states that were part of this conditional block (including itself and its branches).
        """
        processed_states = {state}
        # Filter for InterstateEdges only, as only these have a 'condition' attribute for CFG branching
        interstate_out_edges = [
            e
            for e in parent_sdfg.out_edges(state)
            if isinstance(e, dace.InterstateEdge)
        ]
        out_edges = sorted(
            interstate_out_edges,
            key=lambda e: str(e.condition if e.condition is not None else ""),
        )

        if not out_edges or all(e.condition is None for e in out_edges):
            # Not a conditional branch, or only unconditional edges
            # For now, we only handle explicit conditionals here.
            return set()

        # Group edges by condition and identify the 'else' branch if present
        conditional_edges_with_conditions = []
        unconditional_else_edge = None

        for edge in out_edges:
            if edge.condition is not None and str(edge.condition) != "1":
                conditional_edges_with_conditions.append(edge)
            elif (
                edge.condition is None or str(edge.condition) == "1"
            ):  # An unconditional edge might serve as the 'else'
                unconditional_else_edge = edge

        # Ensure consistent ordering for if/elif/else by sorting conditional edges
        conditional_edges_with_conditions.sort(key=lambda e: str(e.condition))

        if not conditional_edges_with_conditions and not unconditional_else_edge:
            # Not a conditional branch with explicit conditions or an 'else'
            return set()

        # Determine source states for arrays that are read into the conditional block from outside
        source_states: dict[str, str] = {}
        for array_name in self._array_state:
            source_states[array_name] = self._array_state[array_name]

        # These reads/writes are for the conditional statement itself, not its body
        reads_cond_boundary = []
        writes_cond_boundary = []

        read_str = self._convert_accesses_to_pseudocode(reads_cond_boundary)
        write_str = self._convert_accesses_to_pseudocode(writes_cond_boundary)

        stmt_name = self._get_next_stmt_name("C")  # "C" for Conditional

        # Construct source_states string for pseudocode
        unique_source_stmts = sorted(list(set(source_states.values())))
        filtered_source_stmts = [s for s in unique_source_stmts if s != "."]
        dataflow_prefix = (
            f"()."
            if not filtered_source_stmts
            else f"({', '.join(filtered_source_stmts)})."
        )

        # Store initial _array_state to restore for each branch
        initial_array_state_for_branches = self._array_state.copy()
        array_states_after_branches: list[dict[str, str]] = []

        self._current_array_state_stack.append(self._current_scope_stmt_name)
        self._current_scope_stmt_name = (
            stmt_name  # The conditional itself is the parent for its body
        )

        for i, edge in enumerate(conditional_edges_with_conditions):
            # Restore _array_state to the state before the conditional block for each branch
            self._array_state = initial_array_state_for_branches.copy()
            processed_states.add(edge.dst)  # Mark destination state as processed

            cond_str = self._convert_sympy_boolean_to_pseudocode(edge.condition)
            if i == 0:  # First conditional branch is 'if'
                self._add_line(
                    f"({read_str} => {write_str}) {dataflow_prefix}{stmt_name}| if {cond_str}:"
                )
            else:  # Subsequent conditional branches are 'else if'
                self._add_line(f"else if {cond_str}:")

            self._indent_level += 1
            self._convert_cfg_node(
                edge.dst, parent_sdfg
            )  # Process the branch's destination state
            self._indent_level -= 1
            array_states_after_branches.append(self._array_state.copy())

        # Handle the 'else' branch if it exists
        if unconditional_else_edge:
            self._array_state = initial_array_state_for_branches.copy()
            processed_states.add(
                unconditional_else_edge.dst
            )  # Mark destination state as processed

            self._add_line(f"else:")

            self._indent_level += 1
            self._convert_cfg_node(unconditional_else_edge.dst, parent_sdfg)
            self._indent_level -= 1
            array_states_after_branches.append(self._array_state.copy())

        # Merge _array_state after all branches
        merged_array_state = initial_array_state_for_branches.copy()
        modified_arrays_in_any_branch = set()

        for branch_state in array_states_after_branches:
            for array_name, producer_stmt in branch_state.items():
                if initial_array_state_for_branches.get(array_name) != producer_stmt:
                    modified_arrays_in_any_branch.add(array_name)

        for array_name in modified_arrays_in_any_branch:
            merged_array_state[array_name] = (
                stmt_name  # The conditional block is the new producer
            )

        self._array_state = merged_array_state
        self._current_scope_stmt_name = self._current_array_state_stack.pop()

        return processed_states

    def convert(self) -> str:
        """
        Initiates the conversion of the SDFG to a P3G pseudocode string.
        """
        # 1. Declarations (decl, sym, var) should be collected first
        # This is a two-pass approach: first traverse to collect vars, then print.
        # So we collect vars during the main traversal and print them here.
        self._collect_all_declarations_and_outputs()

        # Now, print them
        self._print_declarations()
        self._print_outputs()

        self._add_line("")  # Newline for separation

        # 3. Traverse the SDFG's top-level control flow graph (CFG)
        for node in dfs_topological_sort(self.sdfg):
            self._convert_cfg_node(node, self.sdfg)

        return "\n".join(self.pseudocode_lines)

    def _extract_sympy_symbols(self, expr: sp.Expr):
        """
        Recursively extracts all unique sympy.Symbol instances from an expression
        and adds their string representation to self._declared_symbols,
        excluding P3G_KEYWORDS.
        Also, identifies `sympy.Indexed` instances and adds their base names
        to `self._declared_arrays` if they are not already present.
        """
        if isinstance(expr, sp.Symbol):
            sym_name = str(expr)
            if sym_name not in P3G_KEYWORDS:
                self._declared_symbols.add(sym_name)
        elif isinstance(expr, sp.Indexed):
            array_name = str(expr.base)
            self._declared_arrays.add(array_name)
        elif hasattr(expr, "args"):
            for arg in expr.args:
                self._extract_sympy_symbols(arg)

    def _collect_all_declarations_and_outputs(self):
        # Collect arrays and symbols which are available from sdfg.arrays and sdfg.symbols
        for name, array_desc in self.sdfg.arrays.items():
            if array_desc.shape == ():  # 0-dimensional array, treat as scalar
                self._declared_symbols.add(name)
            else:
                self._declared_arrays.add(name)
        self._declared_symbols.update(str(s) for s in self.sdfg.symbols.keys())

        # To collect loop variables and other symbols from expressions, we need to traverse the SDFG.
        for node in dfs_topological_sort(self.sdfg):
            self._traverse_for_declarations_in_expressions(node, self.sdfg)

    def _traverse_for_declarations_in_expressions(self, node, sdfg_context):
        # Collect loop variables and extract symbols from expressions.
        if isinstance(node, MapEntry):
            map_ = node.map

            for param in map_.params:
                self._declared_loop_vars.add(param)
            # Extract symbols from map range expressions
            for r in map_.range:
                self._extract_sympy_symbols(r[0])  # Start
                self._extract_sympy_symbols(r[1])  # End
            # Recurse into the map's subgraph
            scope_subgraph = sdfg_context.scope_subgraph(
                node, include_entry=False, include_exit=False
            )
            for sub_node in dfs_topological_sort(scope_subgraph):
                self._traverse_for_declarations_in_expressions(sub_node, sdfg_context)

        elif isinstance(node, LoopRegion):
            self._declared_loop_vars.add(node.loop_variable)
            # Extract symbols from loop bounds
            self._extract_sympy_symbols(get_init_assignment(node))
            self._extract_sympy_symbols(get_loop_end(node))
            # Recurse into the loop region's CFG nodes
            for sub_node in dfs_topological_sort(node):
                self._traverse_for_declarations_in_expressions(sub_node, node)

        elif isinstance(node, ConditionalBlock):
            for dace_cond_codeblock, branch_cfg in node.branches:
                if dace_cond_codeblock is not None and dace_cond_codeblock.code != "1":
                    # Extract symbols from condition expression
                    sympy_cond_expr = self._parse_code_block_to_sympy(
                        dace_cond_codeblock
                    )
                    self._extract_sympy_symbols(sympy_cond_expr)
                for sub_node in dfs_topological_sort(branch_cfg):
                    self._traverse_for_declarations_in_expressions(sub_node, branch_cfg)

        elif isinstance(node, NestedSDFG):
            # Recurse into the nested SDFG
            nested_converter = SDFGToPseudocodeConverter(node.sdfg)
            nested_converter._collect_all_declarations_and_outputs()
            self._declared_arrays.update(nested_converter._declared_arrays)
            self._declared_symbols.update(nested_converter._declared_symbols)
            self._declared_loop_vars.update(nested_converter._declared_loop_vars)
            # Extract symbols from symbol mappings in NestedSDFG
            for sym_name_or_expr in node.symbol_mapping.values():
                try:
                    # Attempt to sympify if it's a string, otherwise assume it's already a SymPy object
                    sym_expr = sp.sympify(sym_name_or_expr)
                    self._extract_sympy_symbols(sym_expr)
                except sp.SympifyError:
                    # If it cannot be sympified, it might be a literal string or another non-symbolic type, ignore it
                    pass

        elif isinstance(node, SDFGState):
            # Recurse into dataflow nodes of the state
            for sub_node in dfs_topological_sort(node):
                if isinstance(sub_node, MapEntry):
                    # Recurse into the map's subgraph within the current state
                    self._traverse_for_declarations_in_expressions(sub_node, node)
                elif isinstance(sub_node, NestedSDFG):
                    # Recurse into the nested SDFG object itself
                    self._traverse_for_declarations_in_expressions(
                        sub_node, sub_node.sdfg
                    )

    def _print_declarations(self):
        """Generates decl, sym, and var statements."""
        # Arrays
        all_arrays = sorted(list(self._declared_arrays))
        if all_arrays:
            self._add_line(f"decl {', '.join(all_arrays)}")

        # Loop variables
        all_loop_vars = sorted(list(self._declared_loop_vars))

        # Symbols - exclude loop variables
        all_symbols = sorted(list(self._declared_symbols - self._declared_loop_vars))
        if all_symbols:
            self._add_line(f"sym {', '.join(all_symbols)}")

        if all_loop_vars:
            self._add_line(f"var {', '.join(all_loop_vars)}")

    def _print_outputs(self):
        """Generates the out statement."""
        output_arrays = sorted(
            [name for name, desc in self.sdfg.arrays.items() if not desc.transient]
        )
        if output_arrays:
            self._add_line(f"out {', '.join(output_arrays)}")
