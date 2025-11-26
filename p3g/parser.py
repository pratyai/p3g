# p3g/parser.py

from __future__ import annotations

import collections
import re

from pysmt.shortcuts import (
    INT,
    Plus,
    Minus,
    Int,
    GT,
    LE,
    LT,
    GE,
    Equals,
    Not,
    Select,
    ArrayType,
    ForAll,
    Exists,
    And,
    Or,
    Implies,
    Times,
    Symbol,
)

from p3g.graph import (
    GraphBuilder,
    Graph,
    Data,
    PysmtFormula,
    PysmtRange,
    PysmtCoordSet,
    PysmtAccessSubset,
)

Token = collections.namedtuple("Token", ["type", "value", "line", "column"])


class PseudocodeParser:
    """
    Parses a pseudocode-like language into a P3G graph using a recursive
    descent strategy. This is a simple frontend for the P3G tool.
    """

    def __init__(self):
        self.builder = GraphBuilder()
        self.known_symbols: dict[str, PysmtFormula] = {}
        self.tokens: list[Token] = []
        self.pos = 0
        self.output_data_names: set[str] = set()
        self._declared_arrays: set[str] = set()  # Track declared arrays
        self._declared_symbols: set[str] = set()  # Track declared symbols
        self._declared_loop_vars: set[str] = set()  # Track declared loop vars

        # Graph -> State -> Array -> Ref.
        self._array_state: dict[tuple[Graph, str, str], Data] = {}
        self._current_array_state_stack: list[str] = ["."]
        self._current_scope_inputs_stack: list[dict[str, Data]] = [{}]

    def parse(self, code: str) -> Graph:
        """
        Parses a block of pseudocode and returns the constructed P3G graph.
        """
        self.tokens = self._tokenize(code)
        self.pos = 0
        self._preprocess_declarations()  # Call the new preprocessing method
        self.pos = 0  # Reset pos for the main parsing pass

        # Populate the initial array state for globally declared arrays
        for array_name in self._declared_arrays:
            initial_data_node = self.builder.add_data(
                array_name,
                pysmt_array_sym=self._get_symbol(f"{array_name}_val"),
            )
            # Mark its producer as the initial state "."
            self._array_state[(self.builder.current_graph, ".", array_name)] = (
                initial_data_node
            )
            # Also add to the initial scope inputs for array access resolution
            self._current_scope_inputs_stack[0][array_name] = initial_data_node

        while self._peek().type in ["DECL", "SYM", "VAR", "OUT", "NEWLINE"]:
            peek_type = self._peek().type
            if peek_type == "DECL":
                self._parse_decl_statement()
            elif peek_type == "SYM":
                self._parse_sym_statement()
            elif peek_type == "VAR":
                self._parse_var_statement()
            elif peek_type == "OUT":
                self._parse_out_statement()
            elif peek_type == "NEWLINE":
                self._consume("NEWLINE")
        self._parse_block()
        self.builder.finish()

        return self.builder.finish()

    # --- Tokenizer ---

    def _tokenize(self, code: str) -> list[Token]:
        """Converts code string into a stream of tokens, handling comments."""
        token_specification = [
            # SMT-LIB specific keywords and types (must come before other keywords and ID)
            ("FORALL", r"forall"),
            ("EXISTS", r"exists"),
            ("AND", r"and"),
            ("OR", r"or"),
            ("NOT", r"not"),
            ("SELECT", r"select"),
            ("INT_TYPE", r"Int"),
            # Keywords (must come before ID)
            ("DECL", r"decl"),
            ("SYM", r"sym"),
            ("VAR", r"var"),
            ("OUT", r"out"),
            ("FOR", r"for"),
            ("TO", r"to"),
            ("IF", r"if"),
            ("ELSE", r"else"),
            ("OP", r"op"),
            # Multi-character operators (must come before single-char ops and ID)
            ("GE", r">="),
            ("LE", r"<="),
            ("ARROW", r"=>"),
            ("EQ", r"="),
            # Single-character operators
            ("GT", r">"),
            ("LT", r"<"),
            ("PIPE", r"\|"),
            ("COLON", r":"),
            ("LPAREN", r"\("),
            ("RPAREN", r"\)"),
            ("LBRACKET", r"\["),
            ("RBRACKET", r"\]"),
            ("PLUS", r"\+"),
            ("MINUS", r"-"),
            ("TIMES", r"\*"),
            ("COMMA", r","),
            ("DOT", r"\."),
            ("BANG", r"!"),
            # Generic identifier (must come after all keywords and multi-char tokens)
            ("ID", r"[A-Za-z_]\w*"),
            # Numbers
            ("NUMBER", r"\d+"),
            ("SKIP", r"[ \t]+"),
            ("MISMATCH", r"."),
        ]
        tok_regex = "|".join("(?P<%s>%s)" % pair for pair in token_specification)
        line_num = 0
        indent_stack = [0]
        tokens = []
        in_block_comment = False  # New flag for block comments

        lines = code.strip().split("\n")
        for line in lines:
            line_num += 1
            original_line = line  # Keep original for column calculation
            stripped_line = line.strip()

            # Handle block comments
            if stripped_line == ";":
                in_block_comment = not in_block_comment
                continue  # Skip this line, it's just a comment delimiter

            if in_block_comment:
                continue  # Skip lines within a block comment

            # Handle line comments
            line_comment_start = stripped_line.find(";")
            if line_comment_start != -1:
                # If the line starts with a comment or has content before it
                line = line[
                    : line.find(";", len(line) - len(stripped_line))
                ]  # Truncate the line at the comment, finding from the start of content

            if not line.strip():  # Check again after comment removal
                continue

            indent = len(line) - len(line.lstrip(" "))
            if indent > indent_stack[-1]:
                indent_stack.append(indent)
                tokens.append(Token("INDENT", indent, line_num, 0))
            while indent < indent_stack[-1]:
                indent_stack.pop()
                tokens.append(Token("DEDENT", indent_stack[-1], line_num, 0))

            if indent != indent_stack[-1]:
                raise IndentationError(
                    "unindent does not match any outer indentation level"
                )

            # Process tokens from the (potentially truncated) line
            processed_line_for_tokenize = line.lstrip(" ")
            current_line_start_col = len(line) - len(processed_line_for_tokenize)

            for mo in re.finditer(tok_regex, processed_line_for_tokenize):
                kind = mo.lastgroup
                value = mo.group()
                # column calculation needs to be relative to the original line
                column = current_line_start_col + mo.start()

                if kind == "SKIP":
                    continue
                if kind == "MISMATCH":
                    raise RuntimeError(f"{value!r} unexpected on line {line_num}")
                tokens.append(Token(kind, value, line_num, column))
            tokens.append(
                Token("NEWLINE", "\n", line_num, len(original_line))
            )  # Use original_line length for NEWLINE

        while len(indent_stack) > 1:
            indent_stack.pop()
            tokens.append(Token("DEDENT", indent_stack[-1], line_num, 0))

        tokens.append(Token("EOF", "", line_num + 1, 0))
        return tokens

    # --- Token Stream Helpers ---

    def _peek(self, offset=0) -> Token:
        if self.pos + offset < len(self.tokens):
            return self.tokens[self.pos + offset]
        return self.tokens[-1]  # EOF

    def _consume(self, expected_type: str | list[str] | None = None) -> Token:
        token = self._peek()
        if isinstance(expected_type, str) and token.type != expected_type:
            raise ValueError(
                f"Expected {expected_type}, got {token.type} at line {token.line}"
            )
        if isinstance(expected_type, list) and token.type not in expected_type:
            raise ValueError(
                f"Expected one of {expected_type}, got {token.type} at line {token.line}"
            )
        self.pos += 1
        return token

    # --- Recursive Descent Parser ---

    def _parse_block(self) -> tuple[list, list]:
        """Parses a block of statements."""
        block_reads = []
        block_writes = []

        while self._peek().type not in ["DEDENT", "EOF"]:
            statement_reads, statement_writes = self._parse_statement()
            block_reads.extend(statement_reads)
            block_writes.extend(statement_writes)

        return block_reads, block_writes

    def _parse_statement(self) -> tuple[list, list]:
        """Parses a single statement."""
        if self._peek().type == "BANG":
            return self._parse_assertion_statement()

        # Parse the access descriptions.
        self._consume("LPAREN")
        hierarchical_reads_raw, _ = self._parse_read_access_list()
        self._consume("ARROW")
        hierarchical_writes_raw, _ = self._parse_write_access_list()
        self._consume("RPAREN")

        # Handle follow_statements and disjoint paths
        follow_statements: list[str] = []
        if self._peek().type == "LPAREN":
            self._consume("LPAREN")
            # Consume comma delimited list of prior statements.
            while self._peek().type != "RPAREN":
                # Bug fix: append value, not token. Also fix comma consumption.
                follow_statements.append(self._consume("ID").value)
                if self._peek().type == "COMMA":
                    self._consume("COMMA")
                else:
                    break  # Exit loop if not a COMMA
            self._consume("RPAREN")
            self._consume("DOT")
        elif self._peek().type == "DOT":
            self._consume("DOT")
            follow_statements = []  # Open a disjoint path.
        else:
            follow_statements = [self._current_array_state_stack[-1]]

        # Determine the node_name (either explicit or generated for anonymous nodes)
        if self._peek().type == "PIPE":
            self._consume("PIPE")
            # Generate a temporary name for anonymous nodes for stack update
            if self._peek().type == "FOR":
                node_name = f"AnonLoop_{self.tokens[self.pos + 1].value}"
            elif self._peek().type == "IF":
                node_name = "AnonBranch"
            elif self._peek().type == "OP":
                node_name = "AnonCompute"
            else:
                node_name = "AnonStmt"  # Fallback
        else:
            node_name = self._consume("ID").value
            self._consume("PIPE")

        # Consolidate the accesses.
        consolidated_reads = []
        for name, subset in hierarchical_reads_raw:
            found_nodes = []
            for state in follow_statements:
                key = (self.builder.current_graph, state, name)
                if key in self._array_state:
                    found_nodes.append(self._array_state[key])

            unique_nodes = list(set(found_nodes))
            assert len(unique_nodes) <= 1, (
                f"Ambiguous read for '{name}'. Found in multiple prior states: {follow_statements}"
            )

            if unique_nodes:
                read_node = unique_nodes[0]
            else:
                dot_key = (self.builder.current_graph, ".", name)
                if dot_key in self._array_state:
                    read_node = self._array_state[dot_key]
                else:
                    read_node = self.builder.add_data(
                        name,
                        pysmt_array_sym=self._get_symbol(f"{name}_val"),
                    )
                    self._array_state[dot_key] = read_node
            consolidated_reads.append((read_node, subset))
        hierarchical_reads = consolidated_reads

        consolidated_writes = []
        for name in {name for name, subset in hierarchical_writes_raw}:
            new_node = self.builder.add_data(
                name,
                pysmt_array_sym=self._get_symbol(f"{name}_val"),
            )
            key = (
                self.builder.current_graph,
                node_name,
                name,
            )  # Use determined node_name here
            self._array_state[key] = new_node

        for name, subset in hierarchical_writes_raw:
            key = (
                self.builder.current_graph,
                node_name,
                name,
            )  # Use determined node_name here
            write_node = self._array_state[key]
            consolidated_writes.append((write_node, subset))
        hierarchical_writes = consolidated_writes

        # Parse the actual statement type and capture its return values
        peek_type = self._peek().type
        if peek_type == "FOR":
            statement_result_reads, statement_result_writes = self._parse_for_loop(
                hierarchical_reads, hierarchical_writes, node_name
            )
        elif peek_type == "IF":
            statement_result_reads, statement_result_writes = self._parse_if_statement(
                hierarchical_reads, hierarchical_writes, node_name
            )
        elif peek_type == "OP":
            statement_result_reads, statement_result_writes = self._parse_op_statement(
                hierarchical_reads, hierarchical_writes, node_name
            )
        elif peek_type == "NEWLINE":
            self._consume("NEWLINE")
            statement_result_reads, statement_result_writes = [], []
        else:
            raise ValueError(
                f"Unsupported or malformed statement starting with {self._peek()}"
            )

        self._current_array_state_stack[-1] = node_name
        return statement_result_reads, statement_result_writes

    def _parse_decl_statement(self):
        """Parses a decl statement: decl A, B, C"""
        self._consume("DECL")

        name = self._consume("ID").value
        self._declared_arrays.add(name)

        while self._peek().type == "COMMA":
            self._consume("COMMA")
            name = self._consume("ID").value
            self._declared_arrays.add(name)

        self._consume("NEWLINE")

    def _parse_out_statement(self):
        """Parses an out statement: out A, B, C"""
        self._consume("OUT")

        name = self._consume("ID").value
        self.builder.mark_array_as_output(name)

        while self._peek().type == "COMMA":
            self._consume("COMMA")
            name = self._consume("ID").value
            self.builder.mark_array_as_output(name)

        self._consume("NEWLINE")

    def _parse_sym_statement(self):
        """Parses a sym statement: sym N, M, ..."""
        self._consume("SYM")
        name = self._consume("ID").value
        self._declared_symbols.add(name)
        self._get_symbol(name)  # Pre-create the symbol

        while self._peek().type == "COMMA":
            self._consume("COMMA")
            name = self._consume("ID").value
            self._declared_symbols.add(name)
            self._get_symbol(name)  # Pre-create the symbol

        self._consume("NEWLINE")

    def _parse_var_statement(self):
        """Parses a var statement: var i, j, ..."""
        self._consume("VAR")
        name = self._consume("ID").value
        self._declared_loop_vars.add(name)

        while self._peek().type == "COMMA":
            self._consume("COMMA")
            name = self._consume("ID").value
            self._declared_loop_vars.add(name)

        self._consume("NEWLINE")

    def _parse_for_loop(
        self,
        hierarchical_reads: list[tuple[Data, PysmtAccessSubset | None]],
        hierarchical_writes: list[tuple[Data, PysmtAccessSubset | None]],
        node_name: str | None,
    ) -> tuple[list, list]:
        """Parses a for loop: for i = start to end: ..."""
        self._consume("FOR")
        var = self._consume("ID").value
        if var not in self._declared_loop_vars:
            raise ValueError(
                f"Loop variable '{var}' was not declared. Use 'var {var}'."
            )
        self._consume("EQ")
        start_formula, start_reads = self._parse_expression()
        self._consume("TO")
        end_formula, end_reads = self._parse_expression()
        self._consume("COLON")
        self._consume("NEWLINE")
        self._consume("INDENT")

        loop_name = node_name if node_name else f"L_{var}"

        with self.builder.add_loop(
            loop_name,
            var,
            start_formula,
            end_formula,
            reads=hierarchical_reads,
            writes=hierarchical_writes,
        ) as loop:
            self.known_symbols[var] = loop.loop_var

            # Populate and push scope inputs
            # Inherit from parent scope (the current top of the stack)
            scope_inputs = self._current_scope_inputs_stack[-1].copy()

            # Augment/override with arrays explicitly passed in the hierarchical_reads of the loop itself
            # These represent the versions of arrays that are *inputs* to this loop scope
            if hierarchical_reads is not None:
                for node, _ in hierarchical_reads:
                    # The 'node' here is already the correct Data object for the version
                    scope_inputs[node.name] = node

            self._current_scope_inputs_stack.append(scope_inputs)

            self._current_array_state_stack.append(".")
            body_reads, body_writes = self._parse_block()
            self._current_array_state_stack.pop()

            self._current_scope_inputs_stack.pop()

        del self.known_symbols[var]
        self._consume("DEDENT")

        return body_reads, body_writes

    def _parse_if_statement(
        self,
        hierarchical_reads: list[tuple[Data, PysmtAccessSubset | None]],
        hierarchical_writes: list[tuple[Data, PysmtAccessSubset | None]],
        node_name: str | None,
    ) -> tuple[list, list]:
        """Parses an if-else statement: if condition: ... else: ..."""
        self._consume("IF")
        has_paren = self._peek().type == "LPAREN"
        if has_paren:
            self._consume("LPAREN")
        # Predicates in if statements are infix conditions
        predicate, condition_reads = self._parse_infix_condition()
        if has_paren:
            self._consume("RPAREN")
        self._consume("COLON")
        self._consume("NEWLINE")
        self._consume("INDENT")

        branch_name = node_name if node_name else f"B_{self.builder.current_graph.name}"

        branch_node = self.builder.add_branch(
            branch_name,
            reads=hierarchical_reads,
            writes=hierarchical_writes,
        )

        total_body_reads, total_body_writes = [], []

        with branch_node.add_path(predicate):
            # Populate and push scope inputs for the 'if' branch
            # Inherit from parent scope (the current top of the stack, which is the scope *before* the if statement)
            scope_inputs = self._current_scope_inputs_stack[-1].copy()

            # Augment/override with arrays explicitly passed in the hierarchical_reads of the if statement itself
            if hierarchical_reads is not None:
                for node, _ in hierarchical_reads:
                    scope_inputs[node.name] = node

            self._current_scope_inputs_stack.append(scope_inputs)

            self._current_array_state_stack.append(".")
            body_reads, body_writes = self._parse_block()
            self._current_array_state_stack.pop()

            self._current_scope_inputs_stack.pop()
            total_body_reads.extend(body_reads)
            total_body_writes.extend(body_writes)

        self._consume("DEDENT")

        if self._peek().type == "ELSE":
            self._consume("ELSE")
            self._consume("COLON")
            self._consume("NEWLINE")
            self._consume("INDENT")

            else_predicate = Not(predicate)
            with branch_node.add_path(else_predicate):
                # Populate and push scope inputs for the 'else' branch
                # Inherit from parent scope (the current top of the stack, which is the scope *before* the if statement)
                scope_inputs = self._current_scope_inputs_stack[-1].copy()

                # Augment/override with arrays explicitly passed in the hierarchical_reads of the if statement itself
                if hierarchical_reads is not None:
                    for node, _ in hierarchical_reads:
                        scope_inputs[node.name] = node

                self._current_scope_inputs_stack.append(scope_inputs)

                self._current_array_state_stack.append(".")
                body_reads, body_writes = self._parse_block()
                self._current_array_state_stack.pop()

                self._current_scope_inputs_stack.pop()
                total_body_reads.extend(body_reads)
                total_body_writes.extend(body_writes)

            self._consume("DEDENT")

        return total_body_reads, total_body_writes

    def _parse_read_access_list(self) -> tuple[list, list]:
        """Parses a comma-separated list of read accesses, e.g., A[i], B[j]."""
        accesses = []
        index_reads = []

        # Handle empty list before arrow
        if self._peek().type in ["ARROW", "RPAREN"]:
            return accesses, index_reads

        access, reads = self._parse_read_access_item()
        accesses.append(access)
        index_reads.extend(reads)

        while self._peek().type == "COMMA":
            self._consume("COMMA")
            access, reads = self._parse_read_access_item()
            accesses.append(access)
            index_reads.extend(reads)

        return accesses, index_reads

    def _parse_write_access_list(self) -> tuple[list, list]:
        """Parses a comma-separated list of write accesses, e.g., A[i], B[j]."""
        accesses = []
        index_reads = []

        # Handle empty list before arrow
        if self._peek().type in ["ARROW", "RPAREN"]:
            return accesses, index_reads

        access, reads = self._parse_write_access_item()
        accesses.append(access)
        index_reads.extend(reads)

        while self._peek().type == "COMMA":
            self._consume("COMMA")
            access, reads = self._parse_write_access_item()
            accesses.append(access)
            index_reads.extend(reads)

        return accesses, index_reads

    def _parse_op_statement(
        self,
        hierarchical_reads: list[tuple[Data, PysmtAccessSubset | None]] | None,
        hierarchical_writes: list[tuple[Data, PysmtAccessSubset | None]] | None,
        node_name: str | None,
    ) -> tuple[list, list]:
        """Parses an op statement: OP(annotation)"""
        self._consume("OP")
        self._consume("LPAREN")
        while self._peek().type != "RPAREN":
            self._consume()  # Consume annotation tokens
        self._consume("RPAREN")
        self._consume("NEWLINE")

        compute_name = node_name if node_name else "compute"
        self.builder.add_compute(
            compute_name, reads=hierarchical_reads, writes=hierarchical_writes
        )
        return hierarchical_reads, hierarchical_writes

    def _parse_assertion_statement(self) -> tuple[list, list]:
        """Parses an assertion statement: ! (SMT_LIB_formula)"""
        self._consume("BANG")

        # The actual parsing of the SMT-LIB formula
        assertion_formula, assertion_reads = self._parse_smt_lib_formula()

        self.builder.add_assertion(assertion_formula)

        self._consume("NEWLINE")
        return [], []

    def _parse_infix_condition(self) -> tuple[PysmtFormula, list]:
        """Parses an infix condition: expr > expr. Used for 'if' statements."""
        lhs_formula, lhs_reads = self._parse_expression()

        op_token = self._consume(["GT", "LT", "GE", "LE", "EQ"])

        rhs_formula, rhs_reads = self._parse_expression()

        op_map = {"GT": GT, "LT": LT, "GE": GE, "LE": LE, "EQ": Equals}
        predicate = op_map[op_token.type](lhs_formula, rhs_formula)

        return predicate, lhs_reads + rhs_reads

    def _parse_smt_lib_formula(self) -> tuple[PysmtFormula, list]:
        """Parses a full SMT-LIB formula, handling quantifiers, logical ops, etc."""
        # SMT-LIB formulas are generally parenthesized, or they are atomic terms (ID, NUMBER)
        token_type = self._peek().type

        if token_type == "LPAREN":
            self._consume("LPAREN")  # Consume the opening parenthesis
            operator_token_type = self._peek().type

            if operator_token_type in ["FORALL", "EXISTS"]:
                formula, reads = self._parse_quantifier()
            elif operator_token_type == "NOT":
                formula, reads = self._parse_not_operator()
            elif operator_token_type in [
                "AND",
                "OR",
                "ARROW",
                "EQ",
                "GT",
                "LT",
                "GE",
                "LE",
                "PLUS",
                "MINUS",
                "TIMES",
                "SELECT",
            ]:
                formula, reads = self._parse_prefix_logical_or_comparison_operator()
            elif operator_token_type == "LPAREN":
                formula, reads = self._parse_smt_lib_formula()
            else:
                raise ValueError(
                    f"Expected SMT-LIB operator or quantifier after '(', got {self._peek().type} at line {self._peek().line}"
                )

            self._consume("RPAREN")
            return formula, reads
        else:
            # Atomic formula: a bare ID (boolean variable), NUMBER, or array access.
            # This is generally used for boolean literals or terms in an expression context.
            # If a comparison (e.g. `x > 0`) is intended, it must be wrapped as `(GT x 0)`.
            if token_type in ["ID", "NUMBER"]:  # Check if it's an ID or NUMBER
                return self._parse_factor()
            else:
                raise ValueError(
                    f"Expected '(' or atomic factor (ID/NUMBER), got {self._peek().type} at line {self._peek().line}"
                )

    def _parse_quantifier(self) -> tuple[PysmtFormula, list]:
        """Parses a quantifier (forall or exists) statement."""
        quantifier_token_type = self._consume(["FORALL", "EXISTS"]).type
        self._consume("LPAREN")  # ( (x1 T1) (x2 T2) ... )

        # Parse bound variables
        bound_vars_list = []
        bound_vars_symbols = []
        original_known_symbols = self.known_symbols.copy()  # Save state for scope

        while self._peek().type == "LPAREN":
            self._consume("LPAREN")
            var_name = self._consume("ID").value
            # For now, all quantifier variables are INT
            var_symbol = Symbol(var_name, INT)
            self.known_symbols[var_name] = (
                var_symbol  # Add to known symbols for formula parsing
            )
            bound_vars_list.append(var_symbol)
            self._consume("INT_TYPE")  # Consume the type 'Int'
            self._consume("RPAREN")
        self._consume("RPAREN")

        # Parse the body of the quantified formula
        body_formula, body_reads = self._parse_smt_lib_formula()

        # Restore known_symbols state after quantifier scope
        self.known_symbols = original_known_symbols

        if quantifier_token_type == "FORALL":
            return ForAll(bound_vars_list, body_formula), body_reads
        else:  # EXISTS
            return Exists(bound_vars_list, body_formula), body_reads

    def _parse_not_operator(self) -> tuple[PysmtFormula, list]:
        """Parses a NOT operator: (not formula)"""
        self._consume("NOT")
        formula, reads = self._parse_smt_lib_formula()
        return Not(formula), reads

    def _parse_prefix_logical_or_comparison_operator(self) -> tuple[PysmtFormula, list]:
        """Parses prefix logical (and, or, =>) or comparison (>, <, =, >=, <=) operators."""
        op_token_type = self._consume(
            [
                "AND",
                "OR",
                "ARROW",
                "EQ",
                "GT",
                "LT",
                "GE",
                "LE",
                "PLUS",
                "MINUS",
                "TIMES",
                "SELECT",
            ]
        ).type

        args = []
        all_reads = []
        while self._peek().type != "RPAREN":
            arg_formula, arg_reads = self._parse_smt_lib_formula()
            args.append(arg_formula)
            all_reads.extend(arg_reads)

        if op_token_type == "AND":
            return And(args), all_reads
        elif op_token_type == "OR":
            return Or(args), all_reads
        elif op_token_type == "ARROW":
            if len(args) != 2:
                raise ValueError("Implies operator expects exactly two arguments.")
            return Implies(*args), all_reads
        elif op_token_type in "EQ":
            if len(args) != 2:
                raise ValueError("Equals operator expects exactly two arguments.")
            return Equals(*args), all_reads
        elif op_token_type == "PLUS":
            return Plus(args), all_reads
        elif op_token_type == "MINUS":
            if len(args) != 2:
                raise ValueError("Minus operator expects exactly two arguments.")
            return Minus(*args), all_reads
        elif op_token_type == "TIMES":
            if len(args) != 2:
                raise ValueError("Times operator expects exactly two arguments.")
            return Times(*args), all_reads
        elif op_token_type == "SELECT":
            if len(args) != 2:
                raise ValueError(
                    "Select operator expects exactly two arguments (array, index)."
                )
            return Select(*args), all_reads
        else:  # GT, LT, GE, LE
            op_map = {"GT": GT, "LT": LT, "GE": GE, "LE": LE}
            if len(args) != 2:
                raise ValueError(
                    f"{op_token_type} operator expects exactly two arguments."
                )
            return op_map[op_token_type](*args), all_reads

    def _parse_expression(self) -> tuple[PysmtFormula, list]:
        """Parses an expression: term (+|-) term ..."""
        formula, reads = self._parse_term()
        while self._peek().type in ["PLUS", "MINUS"]:
            op = self._consume().type
            rhs_formula, rhs_reads = self._parse_term()
            reads.extend(rhs_reads)
            if op == "PLUS":
                formula = Plus(formula, rhs_formula)
            else:
                formula = Minus(formula, rhs_formula)
        return formula, reads

    def _parse_term(self) -> tuple[PysmtFormula, list]:
        """Parses a term: factor (TIMES factor)*"""
        formula, reads = self._parse_factor()
        while self._peek().type in ["TIMES"]:
            op = self._consume().type
            rhs_formula, rhs_reads = self._parse_factor()
            reads.extend(rhs_reads)
            if op == "TIMES":
                formula = formula * rhs_formula
        return formula, reads

    def _parse_factor(self) -> tuple[PysmtFormula, list]:
        """Parses a factor: number | symbol | access | (expression)"""
        if self._peek().type == "NUMBER":
            return Int(int(self._consume("NUMBER").value)), []
        if self._peek().type == "ID":
            if self._peek(1).type == "LBRACKET":
                return self._parse_array_access_expression()
            name = self._consume("ID").value
            return self._get_symbol(name), []
        if self._peek().type == "LPAREN":
            self._consume("LPAREN")
            formula, reads = self._parse_expression()
            self._consume("RPAREN")
            return formula, reads
        if self._peek().type == "MINUS":  # Handle unary minus
            self._consume("MINUS")
            formula, reads = (
                self._parse_factor()
            )  # Recursively parse the factor being negated
            return Minus(Int(0), formula), reads  # Represent as 0 - formula
        raise ValueError(
            f"Unsupported or malformed factor starting with {self._peek()}"
        )

    def _parse_access_item(self) -> tuple[PysmtFormula | PysmtRange, list]:
        """Parses a single item in an access list, which can be an expression, a range, or '?' for inference."""
        start_formula, start_reads = self._parse_expression()
        if self._peek().type == "COLON":
            # This is a range
            self._consume("COLON")
            end_formula, end_reads = self._parse_expression()
            return PysmtRange(start_formula, end_formula), start_reads + end_reads
        else:
            return start_formula, start_reads

    def _parse_read_access_item(
        self,
    ) -> tuple[tuple[str, PysmtFormula | PysmtCoordSet | PysmtRange], list]:
        """Parses a single read access, returning the (array name, subset) and any reads from indices."""
        name = self._consume("ID").value
        self._consume("LBRACKET")

        items, reads = [], []
        item, item_reads = self._parse_access_item()
        items.append(item)
        reads.extend(item_reads)

        while self._peek().type == "COMMA":
            self._consume("COMMA")
            item, item_reads = self._parse_access_item()
            items.append(item)
            reads.extend(item_reads)
        self._consume("RBRACKET")

        # Now returns the parsed name and coordinate, not a Data node
        coord = items[0] if len(items) == 1 else PysmtCoordSet(*items)
        return (name, coord), reads

    def _parse_write_access_item(
        self,
    ) -> tuple[tuple[str, PysmtFormula | PysmtCoordSet | PysmtRange], list]:
        """Parses a LHS array access, returning the (array name, subset) and any reads from indices."""
        name = self._consume("ID").value
        self._consume("LBRACKET")

        items, reads = [], []
        item, item_reads = self._parse_access_item()
        items.append(item)
        reads.extend(item_reads)

        while self._peek().type == "COMMA":
            self._consume("COMMA")
            item, item_reads = self._parse_access_item()
            items.append(item)
            reads.extend(item_reads)
        self._consume("RBRACKET")

        # Now returns the parsed name and coordinate, not a Data node
        coord = items[0] if len(items) == 1 else PysmtCoordSet(*items)
        return (name, coord), reads

    def _parse_array_access_expression(self) -> tuple[PysmtFormula, list]:
        """Parses a RHS array access, returning the formula and all reads."""
        name = self._consume("ID").value
        self._consume("LBRACKET")

        indices, reads = [], []
        idx_formula, idx_reads = self._parse_expression()
        indices.append(idx_formula)
        reads.extend(idx_reads)
        while self._peek().type == "COMMA":
            self._consume("COMMA")
            idx_formula, idx_reads = self._parse_expression()
            indices.append(idx_formula)
            reads.extend(idx_reads)
        self._consume("RBRACKET")

        data_node = self._current_scope_inputs_stack[-1][name]
        coord = indices[0] if len(indices) == 1 else PysmtCoordSet(*indices)
        reads.insert(0, (data_node, coord))

        # For formula generation, only single-dim access is supported for now
        if len(indices) > 1:
            raise NotImplementedError(
                "Multi-dim access in expressions not supported for formula generation."
            )

        array_sym = self._get_symbol(f"{name}_val")
        formula = Select(array_sym, indices[0])

        return formula, reads

    # --- Helpers ---

    def _get_symbol(self, name: str) -> PysmtFormula:
        """Gets or creates a PysmtSymbol, enforcing declaration-before-use."""
        if name in self.known_symbols:
            return self.known_symbols[name]

        # Check if it's a declared array's internal SMT array symbol (e.g., A_val)
        if name.endswith("_val"):
            base_name = name.split("_val")[0]
            if base_name in self._declared_arrays:
                sym_type = ArrayType(INT, INT)
                self.known_symbols[name] = self.builder.add_symbol(name, sym_type)
                return self.known_symbols[name]
            else:
                raise ValueError(f"Array '{base_name}' used before being declared.")

        # Check if it's a declared scalar symbol (e.g., N, M)
        if name in self._declared_symbols:
            sym_type = INT  # Regular symbols are INT
            self.known_symbols[name] = self.builder.add_symbol(name, sym_type)
            return self.known_symbols[name]

        # If we reach here, the symbol is undeclared
        raise ValueError(
            f"Symbol '{name}' not declared. Use 'sym {name}' or 'decl {name}' for arrays."
        )

    def _preprocess_declarations(self):
        temp_pos = 0
        while temp_pos < len(self.tokens):
            token = self.tokens[temp_pos]
            if token.type == "DECL":
                # Temporarily parse DECL statement
                current_pos = self.pos
                self.pos = temp_pos
                self._consume("DECL")
                name = self._consume("ID").value
                self._declared_arrays.add(name)
                while self._peek().type == "COMMA":
                    self._consume("COMMA")
                    name = self._consume("ID").value
                    self._declared_arrays.add(name)
                self._consume("NEWLINE")
                temp_pos = self.pos  # Advance temp_pos past the statement
                self.pos = current_pos  # Restore original pos
            elif token.type == "SYM":
                # Temporarily parse SYM statement
                current_pos = self.pos
                self.pos = temp_pos
                self._consume("SYM")
                name = self._consume("ID").value
                self._declared_symbols.add(name)
                self._get_symbol(name)  # Pre-create the symbol
                while self._peek().type == "COMMA":
                    self._consume("COMMA")
                    name = self._consume("ID").value
                    self._declared_symbols.add(name)
                    self._get_symbol(name)  # Pre-create the symbol
                self._consume("NEWLINE")
                temp_pos = self.pos  # Advance temp_pos past the statement
                self.pos = current_pos  # Restore original pos
            elif token.type == "VAR":
                # Temporarily parse VAR statement
                current_pos = self.pos
                self.pos = temp_pos
                self._consume("VAR")
                name = self._consume("ID").value
                self._declared_loop_vars.add(name)
                while self._peek().type == "COMMA":
                    self._consume("COMMA")
                    name = self._consume("ID").value
                    self._declared_loop_vars.add(name)
                self._consume("NEWLINE")
                temp_pos = self.pos  # Advance temp_pos past the statement
                self.pos = current_pos  # Restore original pos
            else:
                temp_pos += 1  # Move to next token if not DECL/OUT/SYM/VAR
