from __future__ import annotations

import ast

import dace
import sympy as sp
from collections import defaultdict
from dace.sdfg import SDFG
from dace.sdfg.nodes import AccessNode, Tasklet, MapEntry, MapExit, NestedSDFG
from dace.sdfg.state import LoopRegion, SDFGState, ConditionalBlock
from dace.sdfg.utils import dfs_topological_sort
from dace.transformation.passes.analysis.loop_analysis import (
    get_loop_end,
    get_init_assignment,
)
import sympy.parsing.sympy_parser

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


class ASTReadExtractor(ast.NodeVisitor):
    def __init__(
        self,
        declared_arrays: set[str],
        promoted_symbols: set[str],
        current_indices: str,
        symbol_definition_indices: dict[str, str],
    ):
        self.reads = []
        self.declared_arrays = declared_arrays
        self.promoted_symbols = promoted_symbols
        self.current_indices = current_indices
        self.symbol_definition_indices = symbol_definition_indices

    def visit_Subscript(self, node):
        array_name = None
        # Extract array name (e.g., A in A[i])
        if isinstance(node.value, ast.Name):
            array_name = node.value.id
        elif isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name):
            # Handle cases like `func(arg)[idx]`, we just take the func name for now
            array_name = node.value.func.id
        # TODO: Handle more complex node.value types if necessary

        if array_name and array_name in self.declared_arrays:
            subset_str = self._convert_slice_to_pseudocode(node.slice)
            self.reads.append((array_name, subset_str))

        # Continue visiting children of the subscript (e.g., expressions within indices)
        self.generic_visit(node)

    def _convert_slice_to_pseudocode(self, slice_node) -> str:
        if isinstance(slice_node, ast.Index):
            return self._convert_ast_expr_to_pseudocode(slice_node.value)
        elif isinstance(slice_node, ast.Slice):
            lower = (
                self._convert_ast_expr_to_pseudocode(slice_node.lower)
                if slice_node.lower
                else ""
            )
            upper = (
                self._convert_ast_expr_to_pseudocode(slice_node.upper)
                if slice_node.upper
                else ""
            )
            # P3G range syntax does not support step
            return f"{lower}:{upper}"
        elif isinstance(slice_node, ast.ExtSlice):
            parts = []
            for dim in slice_node.dims:
                parts.append(self._convert_slice_to_pseudocode(dim))
            return ", ".join(parts)
        elif isinstance(
            slice_node,
            (
                ast.BinOp,
                ast.Name,
                ast.Constant,
                ast.Call,
                ast.UnaryOp,
                ast.Compare,
                ast.BoolOp,
                ast.Tuple,
                ast.List,
            ),
        ):
            # If the slice itself is an expression, convert it directly.
            # This handles cases like `arr[i + j]` where the index is a direct BinOp,
            # or `arr[N]` where the index is a Name, or `arr[1]` where it's a Constant.
            return self._convert_ast_expr_to_pseudocode(slice_node)
        else:
            raise NotImplementedError(
                f"Unsupported slice type: {type(slice_node).__name__}"
            )

    def _convert_ast_expr_to_pseudocode(self, ast_expr_node) -> str:
        # Recursively convert simple AST expressions (numbers, names, binops, etc.) to strings
        if ast_expr_node is None:
            return ""
        elif isinstance(ast_expr_node, ast.Constant):
            return str(ast_expr_node.value)
        elif isinstance(ast_expr_node, ast.Name):
            # If a name refers to a declared array, it is considered a scalar array access
            # in P3G, so we should append '[0]' or '[indices]' and record the read.
            if ast_expr_node.id in self.declared_arrays:
                indices = "0"
                if ast_expr_node.id in self.promoted_symbols:
                    indices = self.symbol_definition_indices.get(ast_expr_node.id, "0")

                self.reads.append((ast_expr_node.id, indices))
                return f"{ast_expr_node.id}[{indices}]"
            return ast_expr_node.id
        elif isinstance(ast_expr_node, ast.BinOp):
            left = self._convert_ast_expr_to_pseudocode(ast_expr_node.left)
            right = self._convert_ast_expr_to_pseudocode(ast_expr_node.right)
            op = self._convert_ast_op_to_str(ast_expr_node.op)
            # Add parentheses for correct precedence if necessary
            if isinstance(ast_expr_node.op, (ast.Add, ast.Sub)) and isinstance(
                ast_expr_node.left, (ast.Mult, ast.Div, ast.FloorDiv, ast.Mod, ast.Pow)
            ):
                return f"({left} {op} {right})"
            return f"{left} {op} {right}"
        elif isinstance(ast_expr_node, ast.UnaryOp):
            operand = self._convert_ast_expr_to_pseudocode(ast_expr_node.operand)
            op = self._convert_ast_unary_op_to_str(ast_expr_node.op)
            return f"{op}{operand}"
        elif isinstance(ast_expr_node, ast.Call):
            func_name = self._convert_ast_expr_to_pseudocode(ast_expr_node.func)
            args = ", ".join(
                self._convert_ast_expr_to_pseudocode(arg) for arg in ast_expr_node.args
            )
            return f"{func_name}({args})"
        elif isinstance(ast_expr_node, ast.Compare):
            left = self._convert_ast_expr_to_pseudocode(ast_expr_node.left)
            ops = [self._convert_ast_op_to_str(op) for op in ast_expr_node.ops]
            comparators = [
                self._convert_ast_expr_to_pseudocode(comp)
                for comp in ast_expr_node.comparators
            ]
            # Handle multiple comparisons: A > B > C => A > B and B > C
            result = []
            # First comparison
            result.append(f"{left} {ops[0]} {comparators[0]}")
            # Chained comparisons
            for i in range(1, len(ops)):
                result.append(f"{comparators[i - 1]} {ops[i]} {comparators[i]}")
            return " and ".join(result)
        elif isinstance(ast_expr_node, ast.BoolOp):
            op = " and " if isinstance(ast_expr_node.op, ast.And) else " or "
            values = [
                self._convert_ast_expr_to_pseudocode(val)
                for val in ast_expr_node.values
            ]
            return f"({op.join(values)})"
        elif isinstance(
            ast_expr_node, ast.Subscript
        ):  # Nested subscript, e.g. B[A[i]] or A[B[0]]
            # This is an indirect access. We need to record this access itself.
            array_name = None
            if isinstance(ast_expr_node.value, ast.Name):
                array_name = ast_expr_node.value.id
            elif isinstance(ast_expr_node.value, ast.Call) and isinstance(
                ast_expr_node.value.func, ast.Name
            ):
                array_name = ast_expr_node.value.func.id

            if array_name and array_name in self.declared_arrays:
                subset_str = self._convert_slice_to_pseudocode(ast_expr_node.slice)
                self.reads.append((array_name, subset_str))

            # Then return its string representation
            return f"{self._convert_ast_expr_to_pseudocode(ast_expr_node.value)}[{self._convert_slice_to_pseudocode(ast_expr_node.slice)}]"

        elif isinstance(ast_expr_node, ast.Tuple):
            elements = ", ".join(
                self._convert_ast_expr_to_pseudocode(e) for e in ast_expr_node.elts
            )
            return elements
        elif isinstance(ast_expr_node, ast.List):
            elements = ", ".join(
                self._convert_ast_expr_to_pseudocode(e) for e in ast_expr_node.elts
            )
            return f"[{elements}]"
        else:
            raise NotImplementedError(
                f"Unsupported AST expression type: {type(ast_expr_node).__name__}"
            )

    def _convert_ast_op_to_str(self, op_node):
        if isinstance(op_node, ast.Add):
            return "+"
        if isinstance(op_node, ast.Sub):
            return "-"
        if isinstance(op_node, ast.Mult):
            return "*"
        if isinstance(op_node, ast.Div):
            return "/"
        if isinstance(op_node, ast.FloorDiv):
            return "//"  # P3G SYNTAX.md lists //
        if isinstance(op_node, ast.Mod):
            return "%"
        if isinstance(op_node, ast.Pow):
            return "^"  # P3G uses ^ for power
        if isinstance(op_node, ast.Eq):
            return "="  # P3G uses = for equality
        if isinstance(op_node, ast.NotEq):
            return "!="
        if isinstance(op_node, ast.Lt):
            return "<"
        if isinstance(op_node, ast.LtE):
            return "<="
        if isinstance(op_node, ast.Gt):
            return ">"
        if isinstance(op_node, ast.GtE):
            return ">="
        if isinstance(op_node, ast.Is):
            raise ValueError(
                "Unsupported binary operator 'is'. Identity comparisons are not part of P3G pseudocode syntax."
            )
        if isinstance(op_node, ast.IsNot):
            raise ValueError(
                "Unsupported binary operator 'is not'. Identity comparisons are not part of P3G pseudocode syntax."
            )
        if isinstance(op_node, ast.In):
            raise ValueError(
                "Unsupported binary operator 'in'. Membership tests are not part of P3G pseudocode syntax."
            )
        if isinstance(op_node, ast.NotIn):
            raise ValueError(
                "Unsupported binary operator 'not in'. Membership tests are not part of P3G pseudocode syntax."
            )
        raise NotImplementedError(
            f"Unsupported binary operator: {type(op_node).__name__}"
        )

    def _convert_ast_unary_op_to_str(self, op_node):
        if isinstance(op_node, ast.USub):
            return "-"
        if isinstance(op_node, ast.UAdd):
            return "+"
        if isinstance(op_node, ast.Not):
            return "not "
        if isinstance(op_node, ast.Invert):
            raise ValueError(
                f"Unsupported unary operator (bitwise invert '~'). Bitwise operations are not part of P3G pseudocode syntax."
            )
        raise NotImplementedError(
            f"Unsupported unary operator: {type(op_node).__name__}"
        )


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
        self._promoted_symbols: set[str] = set()

        # Stack to track loop variables for determining indices of promoted symbols
        # Stores (var_name, start_expr, stop_expr, step_expr)
        self._loop_var_stack: list[tuple[str, sp.Expr, sp.Expr, sp.Expr]] = []

        # Map promoted symbol names to their definition indices string (e.g. "i, j")
        self._symbol_definition_indices: dict[str, str] = {}

        # Dataflow tracking
        # Maps array_name to the name of the statement that last wrote to it in the current scope
        self._array_state: dict[str, str] = {}
        # Track writes per statement for conflict resolution
        self._statement_writes: dict[str, set[str]] = defaultdict(set)
        # Stack to manage scope for dataflow (e.g., entering/exiting loops, branches)
        self._current_array_state_stack: list[str] = ["."]

        # Track processed CFG nodes to avoid redundant processing in conditional branches
        self._processed_cfg_nodes: set[dace.sdfg.nodes.Node] = set()
        self._processed_dataflow_nodes: set[dace.sdfg.nodes.Node] = set()

        self.sympy_global_dict = {
            "GreaterThan": sp.GreaterThan,
            "LessThan": sp.LessThan,
            "StrictGreaterThan": sp.StrictGreaterThan,
            "StrictLessThan": sp.StrictLessThan,
            "Equality": sp.Equality,
            "Eq": sp.Eq,
            "Ge": sp.Ge,
            "Gt": sp.Gt,
            "Le": sp.Le,
            "Lt": sp.Lt,  # Added comparison functions
            "And": sp.And,
            "Or": sp.Or,
            "Not": sp.Not,
            "Add": sp.Add,
            "Mul": sp.Mul,
            "Pow": sp.Pow,
            "Float": sp.Float,
            "Integer": sp.Integer,
            "Min": sp.Min,
            "Max": sp.Max,
            "Symbol": sp.Symbol,
            "IndexedBase": sp.IndexedBase,
            "Indexed": sp.Indexed,
            "true": sp.true,
            "false": sp.false,
            "True": sp.true,
            "False": sp.false,
        }

    def _indent(self):
        return "    " * self._indent_level

    def _add_line(self, line: str):
        self.pseudocode_lines.append(self._indent() + line)

    def _get_next_stmt_name(self, prefix: str = "S") -> str:
        name = f"{prefix}{self._next_stmt_id}"
        self._next_stmt_id += 1
        return name

    def _get_current_indices(self) -> str:
        """Returns the current linearized index string based on loop nesting, or '0' if top-level."""
        if not self._loop_var_stack:
            return "0"

        # Calculate linearized index: Sum((var - start) * stride)
        # Stride_k = Product(size_j) for j > k

        linear_index_expr = sp.Integer(0)
        current_stride = sp.Integer(1)

        # Iterate in reverse (innermost to outermost) to build strides
        for var_name, start, stop, step in reversed(self._loop_var_stack):
            # Assuming exclusive stop for size calculation: size = ceiling((stop - start) / step)
            # For simplicity using exact division assuming divisibility, or just (stop-start)/step
            size = (stop - start) / step

            # Index contribution: (var - start) / step * stride
            # Normalized index: (var - start) / step
            var_sym = sp.Symbol(var_name)
            normalized_index = (var_sym - start) / step

            linear_index_expr += normalized_index * current_stride

            current_stride *= size

        return self._convert_sympy_to_pseudocode_expr(
            linear_index_expr, wrap_if_complex=False
        )

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
        elif isinstance(expr, (sp.Float, float)):  # Always cast floats to int
            expr_str = str(int(expr))
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
            if expr_str in self._declared_arrays:
                indices = "0"
                if expr_str in self._promoted_symbols:
                    indices = self._symbol_definition_indices.get(expr_str, "0")
                expr_str = f"{expr_str}[{indices}]"
        elif isinstance(expr, sp.IndexedBase):  # Added handling for IndexedBase
            expr_str = str(expr)
            if expr_str in self._declared_arrays:  # If it's a scalar array (decl)
                indices = "0"
                if expr_str in self._promoted_symbols:
                    indices = self._symbol_definition_indices.get(expr_str, "0")
                expr_str = f"{expr_str}[{indices}]"
            # else: expr_str = str(expr) # Already covered by the default str(expr) below for non-declared IndexedBases

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
            if base in self._promoted_symbols:
                indices = self._symbol_definition_indices.get(base, "0")
            else:
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
        if isinstance(
            sympy_expr, (bool, int, float, sp.Integer, sp.Float)
        ) or sympy_expr in (sp.true, sp.false):
            return []

        accesses = []

        # Always recurse into arguments of compound expressions if they exist
        if isinstance(sympy_expr, sp.Basic):
            for arg in sympy_expr.args:
                accesses.extend(self._get_read_accesses_from_expression(arg))

        if isinstance(sympy_expr, sp.Indexed):
            base_name = str(sympy_expr.base)
            if base_name in self._promoted_symbols:
                indices_str = self._symbol_definition_indices.get(base_name, "0")
            else:
                indices_str = ", ".join(
                    self._convert_sympy_to_pseudocode_expr(idx, wrap_if_complex=False)
                    for idx in sympy_expr.indices
                )
            # Only consider it a read if the base is a declared array
            if base_name in self._declared_arrays:
                accesses.append((base_name, indices_str))
            return accesses

        if isinstance(sympy_expr, sp.Symbol):
            # If it's a symbol that was declared as an array (scalar array in P3G)
            if str(sympy_expr) in self._declared_arrays:
                indices = "0"
                if str(sympy_expr) in self._promoted_symbols:
                    indices = self._symbol_definition_indices.get(str(sympy_expr), "0")
                accesses.append((str(sympy_expr), indices))
            # P3G Symbols (declared via 'sym') are not included in read/write lists.
            return accesses

        # If it's an IndexedBase without indices, it's not a direct access itself.
        # Accesses are collected from Indexed expressions.
        if isinstance(sympy_expr, sp.IndexedBase):
            return accesses

        # Default return in case no specific type matched and no args produced accesses.
        return accesses

    def _parse_code_block_to_sympy(
        self, code_block: dace.properties.CodeBlock
    ) -> sp.Expr:
        """Converts a dace.properties.CodeBlock into a sympy.Expr."""
        code_str = code_block.as_string

        sympy_locals = {str(s): sp.Symbol(s) for s in self.sdfg.free_symbols}

        # Iterate over all declared arrays and determine their SymPy representation
        for name in self._declared_arrays:
            if name in self.sdfg.arrays:  # It's an original SDFG array
                array_desc = self.sdfg.arrays[name]
                if array_desc.shape == ():  # Original 0-dim array (scalar)
                    sympy_locals[name] = sp.Indexed(sp.Symbol(name), 0)
                else:  # Original multi-dim array
                    sympy_locals[name] = sp.IndexedBase(name)
            else:  # It's a promoted scalar array (not an original SDFG array, e.g., _if_cond_0)
                sympy_locals[name] = sp.Indexed(sp.Symbol(name), 0)

        sympy_locals.update(
            {name: sp.Symbol(name) for name in self._declared_loop_vars}
        )
        sympy_locals.update({name: sp.Symbol(name) for name in self._declared_symbols})

        # global_dict as before...

        try:
            return sympy.parsing.sympy_parser.parse_expr(
                code_str,
                local_dict=sympy_locals,
                global_dict=self.sympy_global_dict,
                evaluate=False,
            )
        except (sp.SympifyError, TypeError) as e:
            raise ValueError(
                f"Failed to sympify expression '{code_str}' with provided context: {e}. "
                f"Declared arrays: {self._declared_arrays}, symbols: {self._declared_symbols}, loop vars: {self._declared_loop_vars}"
            ) from e

    def _convert_sympy_boolean_to_pseudocode(self, expr: sp.Expr) -> str:
        """
        Converts a SymPy boolean expression to its pseudocode string representation.
        Handles logical operators, comparisons, boolean literals, and integer literals 0/1.
        """

        def _to_pseudocode_part(sub_expr: sp.Expr, wrap: bool) -> str:
            # Check if the sub_expr is itself a boolean or relational expression
            if sub_expr.is_Boolean:
                return self._convert_sympy_boolean_to_pseudocode(sub_expr)
            else:
                return self._convert_sympy_to_pseudocode_expr(sub_expr, wrap)

        if isinstance(expr, sp.And):
            return " and ".join(
                self._convert_sympy_boolean_to_pseudocode(arg) for arg in expr.args
            )
        elif isinstance(expr, sp.Or):
            return " or ".join(
                self._convert_sympy_boolean_to_pseudocode(arg) for arg in expr.args
            )
        elif isinstance(expr, sp.Not):
            arg_str = _to_pseudocode_part(expr.arg, False)  # Use helper for arg
            # Wrap if the argument is a comparison to ensure correct precedence in 'not (A > B)'
            if isinstance(
                expr.arg,
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
            # Apply the simplification rule for (LHS = 1) -> LHS and (LHS = 0) -> not (LHS)
            if expr.rhs == sp.Integer(1) and (
                expr.lhs.is_Boolean or expr.lhs.is_Relational
            ):
                # Simplify (LHS = 1) to LHS
                # No need to wrap outer LHS if it's already a boolean expression (is_Boolean)
                return _to_pseudocode_part(expr.lhs, False)
            elif expr.rhs == sp.Integer(0) and (
                expr.lhs.is_Boolean or expr.lhs.is_Relational
            ):
                # Simplify (LHS = 0) to not (LHS)
                lhs_str = _to_pseudocode_part(expr.lhs, False)
                # Ensure negation is properly parenthesized if LHS is a complex boolean expression
                if isinstance(
                    expr.lhs,
                    (
                        sp.And,
                        sp.Or,
                        sp.Equality,
                        sp.GreaterThan,
                        sp.LessThan,
                        sp.StrictGreaterThan,
                        sp.StrictLessThan,
                    ),
                ):
                    return f"not ({lhs_str})"
                return f"not {lhs_str}"
            # Original handling for general equality
            return f"{_to_pseudocode_part(expr.lhs, True)} = {_to_pseudocode_part(expr.rhs, True)}"
        elif isinstance(expr, sp.GreaterThan):
            return f"{_to_pseudocode_part(expr.lhs, True)} >= {_to_pseudocode_part(expr.rhs, True)}"
        elif isinstance(expr, sp.LessThan):
            return f"{_to_pseudocode_part(expr.lhs, True)} <= {_to_pseudocode_part(expr.rhs, True)}"
        elif isinstance(expr, sp.StrictGreaterThan):
            return f"{_to_pseudocode_part(expr.lhs, True)} > {_to_pseudocode_part(expr.rhs, True)}"
        elif isinstance(expr, sp.StrictLessThan):
            return f"{_to_pseudocode_part(expr.lhs, True)} < {_to_pseudocode_part(expr.rhs, True)}"
        elif expr == sp.true:
            return "true"
        elif expr == sp.false:
            return "false"
        elif isinstance(expr, sp.Integer):
            if expr == 0:
                return "false"
            elif expr == 1:
                return "true"
            raise ValueError(
                f"Non-boolean integer literal '{expr}' found in boolean context."
            )
        elif isinstance(expr, (sp.Symbol, sp.Indexed)):
            # Assuming symbols/indexed in boolean context refer to boolean variables
            return self._convert_sympy_to_pseudocode_expr(
                expr, wrap_if_complex=False
            )  # No need to wrap a simple boolean var
        else:
            raise ValueError(
                f"Unsupported SymPy expression '{expr}' in boolean context."
            )

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
        # Filter out symbols
        filtered_access_list = [
            (name, subset)
            for name, subset in access_list
            if name not in self._declared_symbols
        ]
        return ", ".join([f"{name}[{subset}]" for name, subset in filtered_access_list])

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

    def _resolve_source_conflicts(
        self, source_states: dict[str, str]
    ) -> dict[str, str]:
        """
        Pass-through: Conflict resolution is now handled by the Parser's 'Latest Wins' logic.
        """
        return source_states

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

        # Resolve conflicts and construct source_states string
        resolved_source_states = self._resolve_source_conflicts(source_states)
        unique_source_stmts = sorted(list(set(resolved_source_states.values())))
        filtered_source_stmts = [s for s in unique_source_stmts if s != "."]

        if not filtered_source_stmts:
            dataflow_prefix = "()."
        else:
            source_states_str = ", ".join(filtered_source_stmts)
            dataflow_prefix = f"({source_states_str})."

        # The syntax for op is: (READS => WRITES) (<source_states>).<stmt_name>| op(<description>)
        label = tasklet.label.replace("(", "{").replace(")", "}")
        self._add_line(
            f"({read_str} => {write_str}) {dataflow_prefix}{stmt_name}| op({label})"
        )

        # After the statement, update the _array_state for all arrays written by this tasklet
        for array_name, _ in current_write_accesses:
            self._array_state[array_name] = stmt_name
            self._statement_writes[stmt_name].add(array_name)

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
        # Map range in DaCe is (start, stop, step)
        # Pushing raw SymPy expressions to stack
        self._loop_var_stack.append((param, map_range[0], map_range[1], map_range[2]))

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

        # Resolve conflicts
        resolved_source_states = self._resolve_source_conflicts(source_states)
        unique_source_stmts = sorted(list(set(resolved_source_states.values())))
        filtered_source_stmts = [s for s in unique_source_stmts if s != "."]

        if not filtered_source_stmts:
            dataflow_prefix = "()."
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
        self._loop_var_stack.pop()

        # Pop scope and restore array state.
        # For arrays written by the map, their state in the outer scope is now this map's statement.
        self._current_scope_stmt_name = self._current_array_state_stack.pop()
        for array_name, _ in writes_map_boundary:
            old_array_state[array_name] = stmt_name
            self._statement_writes[stmt_name].add(array_name)
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

        # Resolve conflicts and construct source_states string
        resolved_source_states = self._resolve_source_conflicts(source_states)
        unique_source_stmts = sorted(list(set(resolved_source_states.values())))
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
        # Propagate declared symbols and arrays so nested converter knows what to filter
        nested_converter._declared_symbols = self._declared_symbols.copy()
        nested_converter._declared_arrays = self._declared_arrays.copy()
        nested_converter._declared_loop_vars = self._declared_loop_vars.copy()
        nested_converter._promoted_symbols = self._promoted_symbols.copy()

        # Propagate loop stack and definition indices for consistent flattening
        nested_converter._loop_var_stack = list(
            self._loop_var_stack
        )  # Shallow copy of list
        nested_converter._symbol_definition_indices = (
            self._symbol_definition_indices.copy()
        )

        # Synchronize Statement IDs
        nested_converter._next_stmt_id = self._next_stmt_id

        # Propagate initial array state to nested converter so it knows sources
        # (This is a simplified mapping assuming matching names)
        nested_converter._array_state = self._array_state.copy()
        # Also need statement writes to check conflicts inside?
        # Maybe safer to let it start fresh or copy?
        # Ideally it should know about external writes to avoid ambiguity if it refers to them.
        nested_converter._statement_writes = self._statement_writes.copy()

        # Run conversion of body
        nested_converter.convert_body()

        # Sync back ID
        self._next_stmt_id = nested_converter._next_stmt_id

        # Append lines to current lines
        self.pseudocode_lines.extend(nested_converter.pseudocode_lines)

        # Update array state from the nested converter's final state
        # This effectively exposes the internal last-writers to the parent scope
        self._array_state.update(nested_converter._array_state)

        # Merge back symbol definitions
        self._symbol_definition_indices.update(
            nested_converter._symbol_definition_indices
        )

        # Merge statement writes
        for k, v in nested_converter._statement_writes.items():
            self._statement_writes[k].update(v)

        # self._current_scope_stmt_name = stmt_name # No wrapper statement to set as scope

    def _emit_assignments_from_edge(self, edge):
        if not isinstance(edge.data, dace.InterstateEdge):
            return

        # Assignments is a dict {var: expr}
        for var, expr in edge.data.assignments.items():
            current_indices = self._get_current_indices()

            expr_ast = ast.parse(expr)
            extractor = ASTReadExtractor(
                self._declared_arrays,
                self._promoted_symbols,
                current_indices,
                self._symbol_definition_indices,
            )
            extractor.visit(expr_ast)

            read_str = self._convert_accesses_to_pseudocode(extractor.reads)
            source_states = {}
            for r_name, _ in extractor.reads:
                source_states[r_name] = self._array_state.get(r_name, ".")

            # Use resolve to be safe/consistent
            resolved = self._resolve_source_conflicts(source_states)

            unique = sorted(list(set(resolved.values())))
            filtered = [s for s in unique if s != "."]
            if not filtered:
                prefix = "()."
            else:
                prefix = f"({', '.join(filtered)})."

            stmt_name = self._get_next_stmt_name("Assign")

            write_indices = "0"
            if var in self._promoted_symbols:
                # The write itself always uses the current loop indices
                write_indices = current_indices

                # Check for conflicts with previously seen definitions, and warn if different
                if var in self._symbol_definition_indices:
                    if self._symbol_definition_indices[var] != current_indices:
                        print(
                            f"WARNING: Symbol '{var}' assigned multiple times with different indices: "
                            f"Previous: '{self._symbol_definition_indices[var]}', Current: '{current_indices}'. "
                            "Updating definition for subsequent usages."
                        )

                # ALWAYS update the definition indices to the current context for this symbol
                # This ensures "latest wins" for subsequent reads
                self._symbol_definition_indices[var] = current_indices

            # Scalar write: var[indices]
            self._add_line(
                f"({read_str} => {var}[{write_indices}]) {prefix}{stmt_name}| op(assign_{var})"
            )

            self._array_state[var] = stmt_name
            self._statement_writes[stmt_name].add(var)

    def _convert_cfg_node(self, node, parent_cfg_node):
        """
        Converts control flow graph (CFG) nodes like SDFGState, LoopRegion, ConditionalBlock.
        `parent_cfg_node` is the SDFG or LoopRegion that contains `node`.
        """
        if node in self._processed_cfg_nodes:
            return

        # Process assignments on incoming edges
        for edge in parent_cfg_node.in_edges(node):
            self._emit_assignments_from_edge(edge)

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

        # Extract bounds as SymPy expressions
        start_sym = get_init_assignment(loop_region)
        stop_sym = get_loop_end(loop_region)
        step_sym = sp.Integer(1)  # Assuming step of 1 as get_loop_step is unavailable

        # LoopRegion bounds: semantics need care.
        # get_loop_end usually returns the comparison value. e.g. i < N -> N.
        # Assuming exclusive upper bound for consistency with Maps and typical size calc.

        self._loop_var_stack.append((loop_var_str, start_sym, stop_sym, step_sym))

        start_expr = self._convert_sympy_to_pseudocode_expr(
            start_sym, wrap_if_complex=True
        )
        end_expr = self._convert_sympy_to_pseudocode_expr(
            stop_sym, wrap_if_complex=True
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

        # Resolve conflicts and construct source_states string
        resolved_source_states = self._resolve_source_conflicts(source_states)
        unique_source_stmts = sorted(list(set(resolved_source_states.values())))
        filtered_source_stmts = [s for s in unique_source_stmts if s != "."]

        if not filtered_source_stmts:
            dataflow_prefix = "()."
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
        self._loop_var_stack.pop()

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
                self._statement_writes[stmt_name].add(array_name)
        self._array_state = old_array_state

    def _convert_conditional_block(self, cond_block: ConditionalBlock, parent_cfg_node):
        # Determine source states for arrays that are read into the conditional block from outside
        source_states: dict[str, str] = {}
        for array_name in self._array_state:
            source_states[array_name] = self._array_state[array_name]

        # These reads/writes are for the conditional statement itself, not its body
        # Collect reads from predicate expressions
        reads_from_predicate = set()
        for dace_cond_codeblock, _ in cond_block.branches:
            if dace_cond_codeblock is not None and dace_cond_codeblock.code != "1":
                sympy_cond_expr = self._parse_code_block_to_sympy(dace_cond_codeblock)
                predicate_accesses = self._get_read_accesses_from_expression(
                    sympy_cond_expr
                )
                for var_name, _ in predicate_accesses:
                    reads_from_predicate.add(var_name)

        final_read_str = self._convert_accesses_to_pseudocode(
            [(v, "0") for v in sorted(list(reads_from_predicate))]
        )
        final_write_str = ""  # Conditional statement itself does not aggregate writes of its branches.

        stmt_name = self._get_next_stmt_name("B")

        # Resolve conflicts and construct source_states string
        resolved_source_states = self._resolve_source_conflicts(source_states)
        unique_source_stmts = sorted(list(set(resolved_source_states.values())))
        filtered_source_stmts = [s for s in unique_source_stmts if s != "."]

        if not filtered_source_stmts:
            dataflow_prefix = "()."
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
                        f"({final_read_str} => {final_write_str}) {dataflow_prefix}{stmt_name}| if {cond_str}:"
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
            self._statement_writes[stmt_name].add(array_name)

        # Update write_str with the determined writes from branches
        write_str = self._convert_accesses_to_pseudocode(
            [(v, "0") for v in sorted(list(modified_arrays_in_any_branch))]
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
        # Collect reads from conditional expressions on edges
        reads_from_predicate = set()
        for edge in conditional_edges_with_conditions:
            if edge.condition is not None and str(edge.condition) != "1":
                # edge.condition is already a sympy.Basic object
                predicate_accesses = self._get_read_accesses_from_expression(
                    edge.condition
                )
                for var_name, _ in predicate_accesses:
                    reads_from_predicate.add(var_name)

        if (
            unconditional_else_edge
            and unconditional_else_edge.condition is not None
            and str(unconditional_else_edge.condition) != "1"
        ):
            # This should not happen for an 'else' edge, but for completeness
            predicate_accesses = self._get_read_accesses_from_expression(
                unconditional_else_edge.condition
            )
            for var_name, _ in predicate_accesses:
                reads_from_predicate.add(var_name)

        read_str = self._convert_accesses_to_pseudocode(
            [(v, "0") for v in sorted(list(reads_from_predicate))]
        )
        write_str = ""  # Conditional statement itself does not aggregate writes of its branches.

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
                    f"({final_read_str} => {final_write_str}) {dataflow_prefix}{stmt_name}| if {cond_str}:"
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
                if sym_name not in self._declared_arrays:
                    # Only add if not already an array
                    self._declared_symbols.add(sym_name)
        elif isinstance(expr, sp.Indexed):
            array_name = str(expr.base)
            self._declared_arrays.add(array_name)
        elif isinstance(expr, sp.Basic):
            for arg in expr.args:
                self._extract_sympy_symbols(arg)

    def _collect_all_declarations_and_outputs(self):
        # Collect arrays and symbols which are available from sdfg.arrays and sdfg.symbols
        for name, array_desc in self.sdfg.arrays.items():
            self._declared_arrays.add(name)  # All SDFG arrays go to declared_arrays
        self._declared_symbols.update(str(s) for s in self.sdfg.symbols.keys())

        # To collect loop variables and other symbols from expressions, we need to traverse the SDFG.
        for node in dfs_topological_sort(self.sdfg):
            self._traverse_for_declarations_in_expressions(node, self.sdfg)

        # Collect symbols assigned on InterstateEdges
        assigned_symbols = set()
        self._collect_assignments_recursive(self.sdfg, assigned_symbols)

        # Treat assigned symbols as scalar arrays (variables)
        # Ensure they are removed from _declared_symbols if present, and added to _declared_arrays
        self._declared_symbols -= assigned_symbols
        self._declared_arrays.update(assigned_symbols)
        self._promoted_symbols.update(assigned_symbols)

        # Final cleanup: ensure no overlap between declared_symbols and declared_arrays
        self._declared_symbols -= self._declared_arrays

    def _collect_assignments_recursive(self, graph, assigned_set):
        for edge in graph.edges():
            if isinstance(edge.data, dace.InterstateEdge):
                for k in edge.data.assignments.keys():
                    assigned_set.add(k)

        for node in graph.nodes():
            if isinstance(node, LoopRegion):
                self._collect_assignments_recursive(node, assigned_set)
            elif isinstance(node, ConditionalBlock):
                for _, body in node.branches:
                    self._collect_assignments_recursive(body, assigned_set)
            elif isinstance(node, NestedSDFG):
                self._collect_assignments_recursive(node.sdfg, assigned_set)
            elif isinstance(node, SDFGState):
                for subnode in node.nodes():
                    if isinstance(subnode, NestedSDFG):
                        self._collect_assignments_recursive(subnode.sdfg, assigned_set)

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
