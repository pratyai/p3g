import re  # Added for normalization
import textwrap

import pytest
from pysmt.shortcuts import get_env, reset_env

from p3g.parser import PseudocodeParser
from tests.cases.graph_definitions import (
    build_array_reversal_graph,
    build_cholesky_sequential_graph,
    build_data_aware_bi_graph,
    build_data_aware_bi_b13_graph,
    build_gauss_seidel_traditional_graph,
    build_indirect_read_gather_graph,
    build_indirect_write_scatter_graph,
    build_long_distance_dependency_graph,
    build_nested_loop_outer_dofs_graph,
    build_nested_loop_inner_dofs_graph,
    build_parallel_loop_graph,
    build_sequential_loop_graph,
    build_sequential_with_symbolic_max_index_graph,
)
from tests.utils import get_p3g_structure_string


@pytest.fixture(autouse=True)
def pysmt_env():
    reset_env()
    get_env().enable_infix_notation = True


def _normalize_graph_string(graph_string: str) -> str:
    """
    Normalizes the string representation of a P3G graph for consistent comparison.
    - Removes dynamic array_id and is_output flags from Data Nodes.
    - Sorts symbols for consistent order.
    - Normalizes loop variable names (replaces 'k' with 'i' for consistency if 'i' is used in pseudocode).
    - Removes 'ID {arr_id}' from predicate reads.
    """
    graph_string = textwrap.dedent(graph_string)
    lines = graph_string.splitlines()
    normalized_lines = []
    for line in lines:
        # Normalize Symbols line: sort and remove 'A_val', 'B_val' if they are not explicitly in the original
        if "### root ### (Symbols:" in line:
            # Extract symbols, sort them, and reconstruct the line
            match = re.search(r"\(Symbols: \[(.*?)\]\)", line)
            if match:
                symbols_str = match.group(1)
                symbols = [
                    s.strip().strip("'") for s in symbols_str.split(",") if s.strip()
                ]
                sorted_symbols = sorted(symbols)
                line = re.sub(
                    r"\(Symbols: \[.*?\]\)", f"(Symbols: {sorted_symbols})", line
                )

        # Normalize Data Nodes line: sort by name
        if "Data Nodes (IDs):" in line:
            match = re.search(r"Data Nodes \(IDs\): (.*)", line)
            if match:
                nodes_str = match.group(1)
                # Split by ', ' to handle multiple nodes
                nodes = [n.strip() for n in nodes_str.split(", ")]
                # Sort by the node name, which is the first part of the string
                sorted_nodes = sorted(nodes, key=lambda x: x.split(" ")[0])
                line = f"  Data Nodes (IDs): {', '.join(sorted_nodes)}"

        # Normalize Loop variable name (k -> i)
        line = line.replace("iter=k", "iter=i")

        # Normalize Predicate Reads: remove 'ID {arr_id}'
        if "> Predicate Reads: ID" in line:
            line = re.sub(r"ID \d+\[", "[", line)

        normalized_lines.append(line)
    return "\n".join(normalized_lines)


class TestPseudocodeParser:
    def test_sequential_loop_parsing(self):
        code = textwrap.dedent("""
            sym N
            var i
            decl A, B
            (A[1:(N-1)], A[2:N], B[2:N] => A[2:N]) L | for i = 2 to N:
              (A[i-1], A[i], B[i] => A[i]) comp | op(A[i] = A[i-1] + B[i])
        """).strip()
        parser = PseudocodeParser()
        graph = parser.parse(code)

        graph_string = get_p3g_structure_string(graph)

        expected_string = textwrap.dedent("""
            ### root ### (Symbols: ['A_val', 'B_val', 'N'])
              Data Nodes (IDs): DATA[A(0)/10001], DATA[A(1)/10001], DATA[B(0)/10002]
              LOOP(L): iter=i in [2, N]
                > Node Reads: A(0)[PysmtRange(1, (N - 1))], A(0)[PysmtRange(2, N)], B(0)[PysmtRange(2, N)]
                > Node Writes: A(1)[PysmtRange(2, N)]
              ### L_body ### (Symbols: [])
                Data Nodes (IDs): DATA[A(2)/10001], DATA[A(3)/10001], DATA[B(1)/10002]
                COMPUTE(comp): Reads=A(2)[(i - 1)], A(2)[i], B(1)[i], Writes=A(3)[i]
        """).strip()

        assert graph_string.strip() == expected_string

    def test_data_aware_bi_parsing(self):
        code = textwrap.dedent("""
            sym N
            var i
            decl A, B
            (A[0:N], A[1:N], B[1:N] => A[1:N]) L | for i = 1 to N:
              (A[i-1], A[i], B[i] => A[i]) B | if B[i] > 0:
                (A[i-1], A[i] => A[i]) comp | op(A[i] = A[i-1])
        """).strip()
        parser = PseudocodeParser()
        graph = parser.parse(code)

        graph_string = get_p3g_structure_string(graph)

        expected_string = textwrap.dedent("""
            ### root ### (Symbols: ['A_val', 'B_val', 'N'])
              Data Nodes (IDs): DATA[A(0)/10001], DATA[A(1)/10001], DATA[B(0)/10002]
              LOOP(L): iter=i in [1, N]
                > Node Reads: A(0)[PysmtRange(0, N)], A(0)[PysmtRange(1, N)], B(0)[PysmtRange(1, N)]
                > Node Writes: A(1)[PysmtRange(1, N)]
              ### L_body ### (Symbols: [])
                Data Nodes (IDs): DATA[A(2)/10001], DATA[A(3)/10001], DATA[B(1)/10002]
                BRANCH(B)
                  > Node Reads: A(2)[(i - 1)], A(2)[i], B(1)[i]
                  > Node Writes: A(3)[i]
                  > Predicate Reads: B[i]
                  - IF: (0 < B_val[i])
                  ### B_branch_0 ### (Symbols: [])
                    Data Nodes (IDs): DATA[A(4)/10001], DATA[A(5)/10001]
                    COMPUTE(comp): Reads=A(4)[(i - 1)], A(4)[i], Writes=A(5)[i]
        """).strip()

        assert graph_string.strip() == expected_string

    def test_named_op_parsing(self):
        code = textwrap.dedent("""
            sym i
            decl A
            (A[i] => A[i]) comp | op(comp)
        """).strip()
        parser = PseudocodeParser()
        graph = parser.parse(code)

        graph_string = get_p3g_structure_string(graph)

        expected_string = textwrap.dedent("""
            ### root ### (Symbols: ['A_val', 'i'])
              Data Nodes (IDs): DATA[A(0)/10001], DATA[A(1)/10001]
              COMPUTE(comp): Reads=A(0)[i], Writes=A(1)[i]
        """).strip()

        assert (
            _normalize_graph_string(graph_string).strip()
            == _normalize_graph_string(expected_string).strip()
        )

        assert (
            _normalize_graph_string(graph_string).strip()
            == _normalize_graph_string(expected_string).strip()
        )

    def test_assertion_parsing(self):
        code = textwrap.dedent("""
            sym N, M, K
            decl A
            out A
            var i
            ! (> N 0)
            ! (= M 10)
            (A[0:K] => A[0:K]) L1 | for i = 0 to K:
                ! (< i M)
                (A[i] => A[i]) S1| op(init)
        """).strip()
        parser = PseudocodeParser()
        graph = parser.parse(code)

        graph_string = get_p3g_structure_string(graph)

        expected_string = textwrap.dedent("""
            ### root ### (Symbols: ['A_val', 'K', 'M', 'N'])
              Data Nodes (IDs): DATA[A(0)/10001], DATA[A(1)/10001]
              Assertions:
                - (0 < N)
                - (M = 10)
              LOOP(L1): iter=i in [0, K]
                > Node Reads: A(0)[PysmtRange(0, K)]
                > Node Writes: A(1)[PysmtRange(0, K)]
              ### L1_body ### (Symbols: [])
                Data Nodes (IDs): DATA[A(2)/10001], DATA[A(3)/10001]
                Assertions:
                  - (i < M)
                COMPUTE(S1): Reads=A(2)[i], Writes=A(3)[i]
        """).strip()

        assert graph_string.strip() == expected_string
        assert len(graph.assertions) == 2
        # Check if the assertions are present and correctly parsed (order might vary based on pysmt internals)
        assertion_strs = [str(a) for a in graph.assertions]
        assert "(0 < N)" in assertion_strs
        assert "(M = 10)" in assertion_strs
        # Additionally check assertion in nested graph
        loop_node = None
        for node in graph.nodes:
            if hasattr(node, "name") and node.name == "L1":
                loop_node = node
                break
        assert loop_node is not None, "L1 loop node not found in graph.nodes"
        assert len(loop_node.nested_graph.assertions) == 1
        assert "(i < M)" in [str(a) for a in loop_node.nested_graph.assertions]

    def test_assertion_parsing_with_arithmetic(self):
        code = textwrap.dedent("""
            sym x, y, z
            ! (and (< x (+ y 1)) (= z (* x y)))
        """).strip()
        parser = PseudocodeParser()
        graph = parser.parse(code)

        graph_string = get_p3g_structure_string(graph)

        expected_string = textwrap.dedent("""
            ### root ### (Symbols: ['x', 'y', 'z'])
              Assertions:
                - ((x < (y + 1)) & (z = (x * y)))
        """).strip()

        assert graph_string.strip() == expected_string
        assert len(graph.assertions) == 1
        assertion_strs = [str(a) for a in graph.assertions]
        assert "((x < (y + 1)) & (z = (x * y)))" in assertion_strs

    def test_assertion_parsing_with_forall(self):
        code = textwrap.dedent("""
            sym N, M
            ! (forall ((x Int)) (=> (and (<= 0 x) (< x N)) (< x M)))
        """).strip()
        parser = PseudocodeParser()
        graph = parser.parse(code)

        graph_string = get_p3g_structure_string(graph)

        expected_string = textwrap.dedent("""
            ### root ### (Symbols: ['M', 'N'])
              Assertions:
                - (forall x . (((0 <= x) & (x < N)) -> (x < M)))
        """).strip()

        normalized_actual = _normalize_graph_string(graph_string).strip()
        normalized_expected = _normalize_graph_string(expected_string).strip()

        assert normalized_actual == normalized_expected
        assert len(graph.assertions) == 1
        assertion_strs = [str(a) for a in graph.assertions]
        assert "(forall x . (((0 <= x) & (x < N)) -> (x < M)))" in assertion_strs

    def test_comment_parsing(self):
        code = textwrap.dedent("""
            ; This is a full line comment
            sym N, M ; inline comment for N, M
            var i ; another inline comment
            decl A, B ; declare arrays
            out A ; specify output

            ;
            This is a block comment
            It spans multiple lines
            ;
            ! (> N 0) ; assertion with inline comment
            (A[0] => A[0]) S1| op(init) ; operation
            ; another comment line
        """).strip()
        parser = PseudocodeParser()
        graph = parser.parse(code)

        graph_string = get_p3g_structure_string(graph)

        expected_string = textwrap.dedent("""
            ### root ### (Symbols: ['A_val', 'B_val', 'M', 'N'])
              Data Nodes (IDs): DATA[A(0)/10001], DATA[A(1)/10001], DATA[B(0)/10002]
              Assertions:
                - (0 < N)
              COMPUTE(S1): Reads=A(0)[0], Writes=A(1)[0]
        """).strip()

        normalized_actual = _normalize_graph_string(graph_string).strip()
        normalized_expected = _normalize_graph_string(expected_string).strip()

        assert normalized_actual == normalized_expected
        assert len(graph.assertions) == 1
        assert "(0 < N)" in [str(a) for a in graph.assertions]

    def test_complex_branch_condition_parsing(self):
        code = textwrap.dedent("""
            sym X, Y, Z, W, A, B, i
            decl C
            (C[0] => C[0]) B | if ((X > Y) and not (Z = W)) or (A < B):
                (C[i] => C[i]) comp | op(C[i] = X)
        """).strip()
        parser = PseudocodeParser()
        try:
            graph = parser.parse(code)
            # Assert that the graph was parsed without exceptions
            assert graph is not None
            # Further assertions can be added here to check the structure if needed
            # For now, just checking for successful parsing
        except Exception as e:
            pytest.fail(f"Parsing failed with exception: {e}")

    def test_keyword_as_symbol_clash(self):
        code = textwrap.dedent("""
            sym N, decl
            decl A
            (A[0] => A[0]) S1| op(init)
        """).strip()
        parser = PseudocodeParser()
        with pytest.raises(ValueError, match="Expected ID, got DECL at line 1"):
            parser.parse(code)

    def test_non_keyword_as_symbol(self):
        code = textwrap.dedent("""
            sym N, decl_i
            decl A
            (A[0] => A[0]) S1| op(init)
        """).strip()
        parser = PseudocodeParser()
        graph = parser.parse(code)
        assert "decl_i" in [str(s) for s in graph.symbols]


class TestGraphDefinitionsParsing:
    """
    Tests the PseudocodeParser against various graph definitions from graph_definitions.py.
    Note: Not all graph definitions can be directly represented by the current PseudocodeParser's
    grammar due to limitations (e.g., lack of support for multiplication/division in expressions,
    complex loop bounds, or advanced scalar variable handling). Only parsable graphs are tested.
    """

    def test_array_reversal_parsing(self):
        code = textwrap.dedent("""
            sym N
            var k
            decl A
            out A
            (A[0:N-1] => A[0:N-1]) L_k | for k = 0 to N-1:
                (A[k], A[N-1-k] => A[k], A[N-1-k]) swap | op(A[k], A[N-1-k] = A[N-1-k], A[k])
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _ = build_array_reversal_graph()
        ref_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == ref_graph_string.strip()

    def test_cholesky_sequential_parsing(self):
        code = textwrap.dedent("""
            sym N
            var i, j
            decl L
            out L
            (L[1:N, 1:(N-1)], L[2:N, 2:N] => L[2:N, 2:N]) L_outer | for i = 2 to N:
              (L[1:i, 1:(i-1)], L[2:i, 2:i] => L[2:i, 2:i]) L_inner | for j = 2 to i:
                (L[i, j-1], L[j-1, j-1], L[i, j] => L[i, j]) T_cholesky | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _ = build_cholesky_sequential_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_data_aware_bi_parsing_from_def(self):
        code = textwrap.dedent("""
            sym N
            var k
            decl A, B
            out A
            (A[0:N-1], A[1:N], B[1:N] => A[1:N]) L1 | for k = 1 to N:
                (A[k-1], A[k], B[k] => A[k]) B1 | if B[k] > 0:
                    (A[k-1], A[k] => A[k]) T1_seq | op(comp)
                (B[k] =>) .B2 | if B[k] <= 0:
                    (=>) T2_skip | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _, _ = build_data_aware_bi_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_data_aware_bi_b13_parsing(self):
        code = textwrap.dedent("""
            sym N
            var k
            decl A, B
            out A
            (A[0:N-1], A[1:N], B[1:N], B[13] => A[1:N]) L1 | for k = 1 to N:
                (A[k-1], A[k], B[k], B[13] => A[k]) B1 | if (B[k] - B[13]) > 0:
                    (A[k-1], A[k] => A[k]) T1_seq | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _, _, _ = build_data_aware_bi_b13_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_gauss_seidel_traditional_parsing(self):
        code = textwrap.dedent("""
            sym N
            var k
            decl A
            out A
            (A[0:N], A[1:N-1] => A[1:N-1]) L1 | for k = 1 to N-1:
                (A[k-1], A[k], A[k+1] => A[k]) T1 | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _ = build_gauss_seidel_traditional_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_indirect_read_gather_parsing(self):
        code = textwrap.dedent("""
            sym N
            var k
            decl A, B, IDX
            out A
            (A[0:N], B[0:N], IDX[0:N] => A[0:N]) L1 | for k = 1 to N:
                (A[k], B[IDX[k]], IDX[k] => A[k]) T1_gather | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _, _, _ = build_indirect_read_gather_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_indirect_write_scatter_parsing(self):
        code = textwrap.dedent("""
            sym N
            var k
            decl A, B, IDX
            out A
            (A[0:N], B[0:N], IDX[0:N] => A[0:N]) L1 | for k = 1 to N:
                (A[IDX[k]], B[k], IDX[k] => A[IDX[k]]) T1_scatter | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _, _, _ = build_indirect_write_scatter_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_long_distance_dependency_parsing(self):
        code = textwrap.dedent("""
            sym N
            var k
            decl A, B
            out A
            (A[0:N], A[2:N], B[2:N] => A[2:N]) L1 | for k = 2 to N:
                (A[k-10], A[k], B[k] => A[k]) B1 | if (k - 10) > 0:
                    (A[k-10], A[k], B[k] => A[k]) T1_gt | op(comp)
                (A[0], A[k], B[k] => A[k]) .B2 | if (k - 10) <= 0:
                    (A[0], A[k], B[k] => A[k]) T2_le | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _ = build_long_distance_dependency_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_nested_loop_outer_dofs_parsing(self):
        code = textwrap.dedent("""
            sym N, M
            var i, j
            decl A, B
            out A
            (A[1:N, 1:M], B[1:N, 1:M] => A[1:N, 1:M]) L_outer | for i = 1 to N:
              (A[i, 1:M], A[i-1, 1:M], B[i, 1:M] => A[i, 1:M]) L_inner | for j = 1 to M:
                (A[i-1, j], A[i, j], B[i, j] => A[i, j]) T_comp | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _, _, _ = build_nested_loop_outer_dofs_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_nested_loop_inner_dofs_parsing(self):
        code = textwrap.dedent("""
            sym N, M
            var i, j
            decl A, B
            out A
            (A[1:N, 1:M], B[1:N, 1:M] => A[1:N, 1:M]) L_outer | for i = 1 to N:
              (A[i, 1:M], B[i, 1:M] => A[i, 1:M]) L_inner | for j = 1 to M:
                (A[i, j-1], A[i, j], B[i, j] => A[i, j]) T_comp | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _, _, _ = build_nested_loop_inner_dofs_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_parallel_loop_parsing(self):
        code = textwrap.dedent("""
            sym N
            var k
            decl A, B, C
            out A
            (A[0:N], B[0:N], C[0:N] => A[0:N]) L1 | for k = 0 to N:
                (A[k], B[k], C[k] => A[k]) T1 | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _, _ = build_parallel_loop_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_sequential_loop_parsing_from_def(self):
        code = textwrap.dedent("""
            sym N
            var k
            decl A, B
            out A
            (A[1:N-1], A[2:N], B[2:N] => A[2:N]) L1 | for k = 2 to N:
                (A[k-1], A[k], B[k] => A[k]) T1 | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _ = build_sequential_loop_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()

    def test_sequential_with_symbolic_max_index_parsing(self):
        code = textwrap.dedent("""
            sym N, w
            var k
            decl A, B
            out A
            (A[0:N], A[2:N], B[2:N] => A[2:N]) L1 | for k = 2 to N:
                (A[k-w], A[k], B[k] => A[k]) B1 | if (k - w) > 0:
                    (A[k-w], A[k], B[k] => A[k]) T1_gt | op(comp)
                (A[0], A[k], B[k] => A[k]) .B2 | if (k - w) <= 0:
                    (A[0], A[k], B[k] => A[k]) T2_le | op(comp)
        """).strip()
        parser = PseudocodeParser()
        parsed_graph = parser.parse(code)
        actual_graph_string = get_p3g_structure_string(parsed_graph)

        # Build the reference graph
        ref_graph, _, _, _, _, _ = build_sequential_with_symbolic_max_index_graph()
        expected_graph_string = get_p3g_structure_string(ref_graph)

        assert actual_graph_string.strip() == expected_graph_string.strip()
