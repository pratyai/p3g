from .decorator import pcode
from .types import sym, var, decl, op, Array, Symbol
from p3g.parser import PseudocodeParser


def test_pcode_decorator_complex():
    N = Symbol("N")
    M = Symbol("M")
    K = Symbol("K")
    A = Array("A")
    B = Array("B")
    C = Array("C")

    @pcode(syms=["N", "M", "K"], decls=["A", "B", "C"], vars=["i", "j", "k"])
    def complex_algo():
        assert N > 0
        for i in range(0, N):
            if i > 0:
                assert M > 0
                for j in range(0, M):
                    if j > i:
                        assert K > 0
                        for k in range(0, K):
                            if k > j:
                                A[i] = B[j] + C[k]
                            elif k == j:
                                A[i] = B[j] * C[k]
                            else:
                                A[i] = C[k] - B[j]

    pcode_str = complex_algo.pcode()
    print(f"\nGenerated pcode:\n---\n{pcode_str}\n---")

    parser = PseudocodeParser()
    try:
        graph = parser.parse(pcode_str)
    except Exception as e:
        assert False, f"P3G Parser failed to parse generated pcode: {e}"

    # Verify root assertions
    root_assertions = [str(a) for a in graph.assertions]
    assert "(0 < N)" in root_assertions

    # Helper to find all nodes recursively
    def find_all_nodes_recursive(graph_obj):
        all_nodes = []
        all_assertions = []
        for node in graph_obj.nodes:
            all_nodes.append(node)
            all_assertions.extend(
                graph_obj.assertions
            )  # Collect assertions from the current graph
            if hasattr(node, "nested_graph") and node.nested_graph:
                nested_nodes, nested_assertions = find_all_nodes_recursive(
                    node.nested_graph
                )
                all_nodes.extend(nested_nodes)
                all_assertions.extend(nested_assertions)
            elif hasattr(node, "branches") and node.branches:
                for _, nested_branch_graph in node.branches:
                    nested_nodes, nested_assertions = find_all_nodes_recursive(
                        nested_branch_graph
                    )
                    all_nodes.extend(nested_nodes)
                    all_assertions.extend(nested_assertions)
        return all_nodes, all_assertions

    all_nodes, all_graph_assertions = find_all_nodes_recursive(graph)

    # Verify loop names
    loop_i_found = False
    loop_j_found = False
    loop_k_found = False

    for node in all_nodes:
        if hasattr(node, "name"):
            if node.name == "L_i":
                loop_i_found = True
            elif node.name == "L_j":
                loop_j_found = True
            elif node.name == "L_k":
                loop_k_found = True

    assert loop_i_found
    assert loop_j_found
    assert loop_k_found

    # Verify nested assertions are present somewhere in the collected assertions
    # The exact placement is verified by the parser successfully parsing it into the graph.
    all_assertion_strs = [str(a) for a in all_graph_assertions]
    assert "(0 < M)" in all_assertion_strs
    assert "(0 < K)" in all_assertion_strs
