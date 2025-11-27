import ast
import inspect
import textwrap

from .analysis import get_accesses


class PCodeTranspiler(ast.NodeVisitor):
    def __init__(self, syms=None, decls=None, vars=None, outs=None):
        self.pcode_lines = []
        self.indent_level = 0

        # Add global declarations if provided
        if syms:
            self.pcode_lines.append(f"sym {', '.join(syms)}")
        if vars:
            self.pcode_lines.append(f"var {', '.join(vars)}")
        if decls:
            self.pcode_lines.append(f"decl {', '.join(decls)}")
        if outs:
            self.pcode_lines.append(f"out {', '.join(outs)}")

    def transpile(self, func):
        source = textwrap.dedent(inspect.getsource(func))
        tree = ast.parse(source)
        if isinstance(tree.body[0], ast.FunctionDef):
            self.visit(tree.body[0])
        else:
            raise ValueError("Expected a function definition")
        return "\n".join(self.pcode_lines)

    def _add_line(self, line):
        indent = "    " * self.indent_level
        self.pcode_lines.append(f"{indent}{line}")

    def visit_FunctionDef(self, node):
        for stmt in node.body:
            self.visit(stmt)

    def _raw_access_list(self, access_list):
        """
        Formats a list of (name, dims, raw_str) tuples into a pcode access string.
        Uses the raw_str (variable indices) directly.
        """

        raw_strings = [item[2] for item in access_list]

        unique_accesses = sorted(list(set(raw_strings)))
        return ", ".join(unique_accesses)

    def _zero_indexed_access_list(self, access_list):
        """
        Formats a list of (name, dims, raw_str) tuples into a pcode access string with zeroed indices.
        e.g., [('A', 1, 'A[i]'), ('B', 2, 'B[j,k]')] -> "A[0], B[0, 0]"
        """
        formatted_set = set()
        for name, dims, _ in access_list:  # Ignore raw_str for zeroing
            zeros = ", ".join(["0"] * dims)
            formatted_set.add(f"{name}[{zeros}]")

        # Sort to ensure deterministic output
        return ", ".join(sorted(list(formatted_set)))

    def visit_Assign(self, node):
        # Check for special declarations: sym, decl, var
        if isinstance(node.value, ast.Call):
            func_name = self._get_func_name(node.value.func)
            if func_name in ["sym", "decl", "var"]:
                args_strs = []
                for arg in node.value.args:
                    if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                        args_strs.append(arg.value)
                if args_strs:
                    self._add_line(f"{func_name} {', '.join(args_strs)}")
                return

        # Otherwise, treat as a computation op
        # A[i] = ...
        reads, writes = get_accesses(node)
        reads.extend(writes)  # P3G Requirement: writes are also reads

        reads_str = self._raw_access_list(reads)
        writes_str = self._raw_access_list(writes)

        # Description is the code itself
        if (
            isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Name)
            and node.value.func.id in ["Symbol", "Array"]
            and node.value.args
            and isinstance(node.value.args[0], ast.Constant)
        ):
            target_str = ast.unparse(node.targets[0])
            symbol_name = node.value.args[0].value
            desc = f"{target_str} = {symbol_name}"
        else:
            desc = ast.unparse(node)

        self._add_line(f"({reads_str} => {writes_str}) | op({desc})")

    def visit_AugAssign(self, node):
        # A[i] += 1
        reads, writes = get_accesses(node)

        # We should manually ensure the target is in both reads and writes for AugAssign.
        if isinstance(node.target, ast.Subscript):
            _, target_writes = get_accesses(node.target)
            if target_writes:
                target_info = target_writes[0]
                if target_info not in reads:
                    reads.append(target_info)
                # target_info is already in writes

        reads_str = self._raw_access_list(reads)
        writes_str = self._raw_access_list(writes)
        # Description is the code itself
        if (
            isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Name)
            and node.value.func.id in ["Symbol", "Array"]
            and node.value.args
            and isinstance(node.value.args[0], ast.Constant)
        ):
            target_str = ast.unparse(node.target)
            symbol_name = node.value.args[0].value
            desc = f"{target_str} = {symbol_name}"  # AugAssign is different, needs specific handling
        else:
            desc = ast.unparse(node)
        self._add_line(f"({reads_str} => {writes_str}) | op({desc})")

    def visit_For(self, node):
        # for i in range(...):
        if (
            not isinstance(node.iter, ast.Call)
            or self._get_func_name(node.iter.func) != "range"
        ):
            raise ValueError("Only 'for ... in range(...)' loops are supported.")

        target_var = ast.unparse(node.target)
        args = node.iter.args

        if len(args) == 1:
            start_str = "0"
            stop_node = args[0]
        elif len(args) >= 2:
            start_str = ast.unparse(args[0])
            stop_node = args[1]
        else:
            raise ValueError("range() requires 1 or 2 arguments")

        # Convert Python range stop value to P3G inclusive end value
        pcode_end_ast_node = ast.BinOp(
            left=stop_node, op=ast.Sub(), right=ast.Constant(1)
        )

        # Attempt to simplify `(X + 1) - 1` to `X` (in AST)
        if (
            isinstance(stop_node, ast.BinOp)
            and isinstance(stop_node.op, ast.Add)
            and isinstance(stop_node.right, ast.Constant)
            and stop_node.right.value == 1
        ):
            pcode_end_ast_node = stop_node.left  # The AST node for X

        # Unparse the simplified AST node
        end_str = ast.unparse(pcode_end_ast_node)

        # Explicitly add parentheses if the expression is not a simple name or constant
        if not isinstance(pcode_end_ast_node, (ast.Name, ast.Constant)):
            end_str = f"({end_str})"

        # Aggregate accesses from body
        reads, writes = get_accesses(node.body)
        reads.extend(
            writes
        )  # P3G requirement: writes are also reads for structural nodes.
        reads_str = self._zero_indexed_access_list(reads)
        writes_str = self._zero_indexed_access_list(writes)

        self._add_line(
            f"({reads_str} => {writes_str}) L_{target_var}| for {target_var} = {start_str} to {end_str}:"
        )

        self.indent_level += 1
        for stmt in node.body:
            self.visit(stmt)
        self.indent_level -= 1

    def visit_If(self, node):
        # Collect all conditions and bodies from the if/elif/else chain
        branches = []
        current_node = node
        while True:
            condition_ast = current_node.test
            body_ast = current_node.body
            branches.append((condition_ast, body_ast))

            if not current_node.orelse:
                break

            if (
                isinstance(current_node.orelse, list)
                and len(current_node.orelse) == 1
                and isinstance(current_node.orelse[0], ast.If)
            ):
                current_node = current_node.orelse[0]
            elif isinstance(current_node.orelse, list):
                # This is the final 'else' block
                branches.append(
                    (None, current_node.orelse)
                )  # None for condition means it's the final 'else'
                break
            else:
                raise ValueError(
                    "Unexpected orelse type in visit_If for non-list orelse."
                )

        # Generate separate B| if statements for each branch with semantically correct predicates
        cumulative_negation_parts_ast = []  # Stores ast nodes of previous conditions for negation
        for condition_ast, body_ast in branches:
            current_effective_condition_parts_ast = []

            # Add negations of all previous conditions (as AST nodes)
            for prev_cond_ast in cumulative_negation_parts_ast:
                current_effective_condition_parts_ast.append(
                    ast.UnaryOp(op=ast.Not(), operand=prev_cond_ast)
                )

            # Add the current condition (as AST node) if it's an 'if' or 'elif'
            if condition_ast:
                current_effective_condition_parts_ast.append(condition_ast)

            # Combine condition parts into a single AST node
            if not current_effective_condition_parts_ast:
                effective_condition_ast = ast.Constant(
                    value=True
                )  # Should only happen for the first 'if' without cumulative negations, or final 'else'
            elif len(current_effective_condition_parts_ast) == 1:
                effective_condition_ast = current_effective_condition_parts_ast[0]
            else:
                effective_condition_ast = ast.BoolOp(
                    op=ast.And(), values=current_effective_condition_parts_ast
                )

            effective_condition_str = self._convert_py_expr_to_pcode_infix(
                effective_condition_ast
            )

            # Aggregate accesses for the body of this specific branch
            reads, writes = get_accesses(body_ast)
            cond_reads, _ = get_accesses(condition_ast) if condition_ast else ([], [])

            reads = reads + cond_reads
            reads.extend(
                writes
            )  # P3G Requirement: writes are also reads for structural nodes.

            reads_str = self._zero_indexed_access_list(reads)
            writes_str = self._zero_indexed_access_list(writes)

            self._add_line(
                f"({reads_str} => {writes_str}) B| if {effective_condition_str}:"
            )

            self.indent_level += 1
            for stmt in body_ast:
                self.visit(stmt)
            self.indent_level -= 1

            # Update cumulative negation for the next branch
            if condition_ast:  # Only add actual conditions to the negation list
                cumulative_negation_parts_ast.append(condition_ast)

    def visit_Expr(self, node):
        # Handle standalone calls like out(A), sym("N")
        if isinstance(node.value, ast.Call):
            self._handle_call(node.value)

    def visit_Assert(self, node):
        # assert condition -> ! (condition)
        # Convert Python expression to SMT-LIB prefix notation
        cond_smt = self._convert_py_expr_to_smt(node.test)
        self._add_line(f"! {cond_smt}")

    def _handle_call(self, node):
        func_name = self._get_func_name(node.func)

        if func_name in ["sym", "decl", "var"]:
            # Standalone declarations
            args_strs = []
            for arg in node.args:
                if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                    args_strs.append(arg.value)
            if args_strs:
                self._add_line(f"{func_name} {', '.join(args_strs)}")

        elif func_name == "out":
            args_strs = []
            for arg in node.args:
                args_strs.append(ast.unparse(arg))
            self._add_line(f"out {', '.join(args_strs)}")

        elif func_name == "assertion":
            if node.args:
                # Convert Python expression to SMT-LIB prefix notation
                cond_smt = self._convert_py_expr_to_smt(node.args[0])
                self._add_line(f"! {cond_smt}")

        # Support explicit op() if mixed in
        elif func_name == "op":
            desc = ast.unparse(node.args[0]).strip("'\"") if node.args else ""
            self._add_line(f"() => () | op({desc})")  # Simplified fallback

    def _get_func_name(self, func_node):
        if isinstance(func_node, ast.Name):
            return func_node.id
        if isinstance(func_node, ast.Attribute):
            return func_node.attr
        return None

    def _convert_py_expr_to_smt(self, expr_node):
        """Converts a Python AST expression node to SMT-LIB prefix notation."""
        if isinstance(expr_node, ast.Compare):
            if len(expr_node.ops) != 1 or len(expr_node.comparators) != 1:
                raise ValueError(
                    "Only simple comparisons (one op, one comparator) are supported for SMT assertions."
                )

            op_map = {
                ast.Gt: ">",
                ast.Lt: "<",
                ast.GtE: ">=",
                ast.LtE: "<=",
                ast.Eq: "=",
                ast.NotEq: "distinct",  # 'distinct' is SMT-LIB for not-equals
            }
            op_str = op_map.get(type(expr_node.ops[0]))
            if not op_str:
                raise ValueError(
                    f"Unsupported comparison operator for SMT: {type(expr_node.ops[0])}"
                )

            left_smt = self._convert_py_expr_to_smt(expr_node.left)
            right_smt = self._convert_py_expr_to_smt(expr_node.comparators[0])
            return f"({op_str} {left_smt} {right_smt})"

        elif isinstance(expr_node, ast.BoolOp):
            op_map = {ast.And: "and", ast.Or: "or"}
            op_str = op_map.get(type(expr_node.op))
            if not op_str:
                raise ValueError(
                    f"Unsupported boolean operator for SMT: {type(expr_node.op)}"
                )

            values_smt = [self._convert_py_expr_to_smt(v) for v in expr_node.values]
            return f"({op_str} {' '.join(values_smt)})"

        elif isinstance(expr_node, ast.Constant):
            if isinstance(expr_node.value, str):
                return expr_node.value  # Return raw string, no quotes
            return ast.unparse(expr_node)
        elif isinstance(expr_node, ast.Name):
            return ast.unparse(expr_node)

        elif isinstance(expr_node, ast.BinOp):
            op_map = {
                ast.Add: "+",
                ast.Sub: "-",
                ast.Mult: "*",
                ast.Div: "/",
                ast.Mod: "mod",
                ast.Pow: "pow",  # Pysmt has Pow, but SMT-LIB 'pow' is usually integer only.
            }
            op_str = op_map.get(type(expr_node.op))
            if not op_str:
                raise ValueError(
                    f"Unsupported arithmetic operator for SMT: {type(expr_node.op)}"
                )

            left_smt = self._convert_py_expr_to_smt(expr_node.left)
            right_smt = self._convert_py_expr_to_smt(expr_node.right)
            return f"({op_str} {left_smt} {right_smt})"

        elif isinstance(expr_node, ast.Subscript):
            if isinstance(expr_node.slice, ast.Slice):
                raise ValueError(
                    "Slice objects (e.g., A[1:5]) are not supported in SMT conversions for assertions."
                )

            array_smt = self._convert_py_expr_to_smt(expr_node.value)
            # For a single index, expr_node.slice can be an ast.Index which has a .value attribute
            # For older Python versions, or if directly an expression, it might be expr_node.slice itself
            index_node = (
                expr_node.slice.value
                if isinstance(expr_node.slice, ast.Index)
                else expr_node.slice
            )
            index_smt = self._convert_py_expr_to_smt(index_node)
            return f"(select {array_smt} {index_smt})"

        else:
            raise ValueError(
                f"Unsupported AST node type for SMT conversion: {type(expr_node).__name__} ({ast.dump(expr_node)})"
            )

    def _convert_py_expr_to_pcode_infix(self, expr_node):
        """Converts a Python AST expression node to PCode infix notation."""
        if isinstance(expr_node, ast.Compare):
            if len(expr_node.ops) != 1 or len(expr_node.comparators) != 1:
                raise ValueError(
                    "Only simple comparisons (one op, one comparator) are supported for PCode."
                )
            left = self._convert_py_expr_to_pcode_infix(expr_node.left)
            op = expr_node.ops[0]
            right = self._convert_py_expr_to_pcode_infix(expr_node.comparators[0])

            if isinstance(op, ast.Eq):
                op_str = "="
            elif isinstance(op, ast.NotEq):
                # PCode doesn't have explicit !=, but parser understands 'not (A = B)'
                op_str = "!="
            elif isinstance(op, ast.Gt):
                op_str = ">"
            elif isinstance(op, ast.Lt):
                op_str = "<"
            elif isinstance(op, ast.LtE):
                op_str = "<="
            elif isinstance(op, ast.GtE):
                op_str = ">="
            else:
                raise ValueError(
                    f"Unsupported comparison operator for PCode: {type(op)}"
                )
            return f"({left} {op_str} {right})"

        elif isinstance(expr_node, ast.BoolOp):
            op_map = {ast.And: "and", ast.Or: "or"}
            op_str = op_map.get(type(expr_node.op))
            if not op_str:
                raise ValueError(
                    f"Unsupported boolean operator for PCode: {type(expr_node.op)}"
                )
            values = [self._convert_py_expr_to_pcode_infix(v) for v in expr_node.values]
            return f"({f' {op_str} '.join(values)})"

        elif isinstance(expr_node, ast.UnaryOp) and isinstance(expr_node.op, ast.Not):
            operand = self._convert_py_expr_to_pcode_infix(expr_node.operand)
            # Add parentheses around the negated expression if it's a comparison or another boolean operation
            if isinstance(expr_node.operand, (ast.Compare, ast.BoolOp, ast.UnaryOp)):
                return f"not ({operand})"
            return f"not {operand}"

        elif isinstance(expr_node, ast.Constant):
            if isinstance(expr_node.value, str):
                return expr_node.value  # Return raw string, no quotes
            return ast.unparse(expr_node)
        elif isinstance(expr_node, ast.Name):
            return ast.unparse(expr_node)

        elif isinstance(expr_node, ast.BinOp):
            # Recursively convert operands and unparse the binary operation
            left = self._convert_py_expr_to_pcode_infix(expr_node.left)
            right = self._convert_py_expr_to_pcode_infix(expr_node.right)
            op_str = ast.unparse(
                expr_node.op
            )  # ast.unparse correctly handles +, -, *, etc.
            return f"({left} {op_str} {right})"

        elif isinstance(expr_node, ast.Subscript):
            return ast.unparse(expr_node)  # ast.unparse should be fine for array access

        elif isinstance(expr_node, ast.Call):
            # This handles function calls like 'range(0, N)' in loops, etc.
            # We should be careful here not to accidentally unparse a call that
            # is meant to be a special PCode construct.
            return ast.unparse(expr_node)

        else:
            raise ValueError(
                f"Unsupported AST node type for PCode infix conversion: {type(expr_node).__name__} ({ast.dump(expr_node)})"
            )
