from pysmt.shortcuts import Symbol, INT, TRUE, And, GE, LE, Plus, Int, simplify

from p3g.p3g import Compute, GraphBuilder, create_path_model_fn


# Helper function to create a simple PysmtFormula for testing
def create_subset_formula(name: str):
    return Symbol(name, INT)


class TestCompute:
    def test_compute_creation(self):
        compute_node = Compute("C1")
        assert compute_node.name == "C1"
        assert repr(compute_node) == "Compute(C1)"

    def test_get_read_write_set(self):
        builder = GraphBuilder()
        A = builder.add_data("A")
        B = builder.add_data("B")
        C = builder.add_data("C")

        c_node = builder.add_compute("C1",
                                     reads=[(A, Int(0)), (B, Int(1))],
                                     writes=[(C, Int(2))])

        read_set = c_node.get_read_set()
        write_set = c_node.get_write_set()

        assert len(read_set) == 3
        assert (A.array_id, Int(0)) in read_set
        assert (B.array_id, Int(1)) in read_set
        assert (C.array_id, Int(2)) in read_set

        assert len(write_set) == 1
        expected_write_set = {
            (C.array_id, Int(2))
        }
        actual_write_set = {item for item in write_set}
        assert actual_write_set == expected_write_set


class TestGraphBuilder:
    def test_builder_init(self):
        builder = GraphBuilder()
        assert builder.root_graph is not None
        assert builder.current_graph == builder.root_graph
        assert builder._next_data_id == 10001

    def test_add_symbol(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        assert "i" in builder.root_graph.symbols
        assert builder.root_graph.symbols["i"] == i

    def test_add_data(self):
        builder = GraphBuilder()
        A = builder.add_data("A")
        B = builder.add_data("B", is_output=True)

        assert A.name == "A"
        assert A.array_id == 10001
        assert A in builder.root_graph.nodes

        assert B.name == "B"
        assert B.array_id == 10002
        assert B in builder.root_graph.nodes
        assert B in builder.root_graph.outputs

    def test_add_compute(self):
        builder = GraphBuilder()
        A = builder.add_data("A")
        B = builder.add_data("B")
        C = builder.add_data("C")

        compute_node = builder.add_compute("C1",
                                           reads=[(A, Int(0))],
                                           writes=[(B, Int(1)), (C, Int(2))])

        assert compute_node in builder.root_graph.nodes
        assert len(compute_node.in_edges) == 3
        expected_in_edges = {
            (A, compute_node, Int(0)),
            (B, compute_node, Int(1)),
            (C, compute_node, Int(2))
        }
        actual_in_edges = {(edge.src, edge.dst, edge.subset) for edge in compute_node.in_edges}
        assert actual_in_edges == expected_in_edges

        assert len(compute_node.out_edges) == 2
        expected_out_edges = {
            (compute_node, B, Int(1)),
            (compute_node, C, Int(2))
        }
        actual_out_edges = {(edge.src, edge.dst, edge.subset) for edge in compute_node.out_edges}
        assert actual_out_edges == expected_out_edges

    def test_add_loop(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_loop("loop1", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]) as loop:
            assert loop.loop_var == i
            assert loop.start == Int(0)
            assert loop.end == N
            assert loop in builder.root_graph.nodes
            assert builder.current_graph == loop.nested_graph

            # Check hierarchical edges
            assert len(loop.in_edges) == 2
            expected_in_edges = {
                (A, loop, i),
                (B, loop, i)
            }
            actual_in_edges = {(edge.src, edge.dst, edge.subset) for edge in loop.in_edges}
            assert actual_in_edges == expected_in_edges

            assert len(loop.out_edges) == 1
            expected_out_edges = {
                (loop, B, i)
            }
            actual_out_edges = {(edge.src, edge.dst, edge.subset) for edge in loop.out_edges}
            assert actual_out_edges == expected_out_edges

            C = builder.add_data("C")
            builder.add_compute("inner_comp", reads=[(A, i)], writes=[(C, i)])

        assert builder.current_graph == builder.root_graph
        assert len(loop.nested_graph.nodes) == 2  # C and inner_comp

    def test_add_map(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_map("map1", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]) as map_node:
            assert map_node.loop_var == i
            assert map_node.start == Int(0)
            assert map_node.end == N
            assert map_node in builder.root_graph.nodes
            assert builder.current_graph == map_node.nested_graph

            # Check hierarchical edges
            assert len(map_node.in_edges) == 2
            expected_in_edges = {
                (A, map_node, i),
                (B, map_node, i)
            }
            actual_in_edges = {(edge.src, edge.dst, edge.subset) for edge in map_node.in_edges}
            assert actual_in_edges == expected_in_edges

            assert len(map_node.out_edges) == 1
            expected_out_edges = {
                (map_node, B, i)
            }
            actual_out_edges = {(edge.src, edge.dst, edge.subset) for edge in map_node.out_edges}
            assert actual_out_edges == expected_out_edges

            C = builder.add_data("C")
            builder.add_compute("inner_comp", reads=[(A, i)], writes=[(C, i)])

        assert builder.current_graph == builder.root_graph
        assert len(map_node.nested_graph.nodes) == 2  # C and inner_comp

    def test_add_branch(self):
        builder = GraphBuilder()
        x = builder.add_symbol("x")
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_branch("branch1", reads=[(A, Int(0))], writes=[(B, Int(0))]) as branch:
            assert branch in builder.root_graph.nodes

            # Check hierarchical edges
            assert len(branch.in_edges) == 2
            expected_in_edges = {
                (A, branch, Int(0)),
                (B, branch, Int(0))
            }
            actual_in_edges = {(edge.src, edge.dst, edge.subset) for edge in branch.in_edges}
            assert actual_in_edges == expected_in_edges

            assert len(branch.out_edges) == 1
            expected_out_edges = {
                (branch, B, Int(0))
            }
            actual_out_edges = {(edge.src, edge.dst, edge.subset) for edge in branch.out_edges}
            assert actual_out_edges == expected_out_edges

            with branch.add_path(GE(x, Int(0))):
                C = builder.add_data("C")
                builder.add_compute("comp_true", reads=[(A, Int(0))], writes=[(C, Int(0))])

            with branch.add_path(LE(x, Int(-1))):
                D = builder.add_data("D")
                builder.add_compute("comp_false", reads=[(A, Int(0))], writes=[(D, Int(0))])

        assert builder.current_graph == builder.root_graph
        assert len(branch.branches) == 2
        assert branch.branches[0][0] == GE(x, Int(0))
        assert branch.branches[1][0] == LE(x, Int(-1))
        assert len(branch.branches[0][1].nodes) == 2  # C and comp_true
        assert len(branch.branches[1][1].nodes) == 2  # D and comp_false

    def test_add_reduce(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_reduce("reduce1", "i", Int(0), N, TRUE(), reads=[(A, i)], writes=[(B, Int(0))]) as reduce_node:
            assert reduce_node.loop_var == i
            assert reduce_node.start == Int(0)
            assert reduce_node.end == N
            assert reduce_node.wcr == TRUE()
            assert reduce_node in builder.root_graph.nodes
            assert builder.current_graph == reduce_node.nested_graph

            # Check hierarchical edges
            assert len(reduce_node.in_edges) == 2
            expected_in_edges = {
                (A, reduce_node, i),
                (B, reduce_node, Int(0))
            }
            actual_in_edges = {(edge.src, edge.dst, edge.subset) for edge in reduce_node.in_edges}
            assert actual_in_edges == expected_in_edges

            assert len(reduce_node.out_edges) == 1
            expected_out_edges = {
                (reduce_node, B, Int(0))
            }
            actual_out_edges = {(edge.src, edge.dst, edge.subset) for edge in reduce_node.out_edges}
            assert actual_out_edges == expected_out_edges

            C = builder.add_data("C")
            builder.add_compute("inner_comp", reads=[(A, i)], writes=[(C, i)])

        assert builder.current_graph == builder.root_graph
        assert len(reduce_node.nested_graph.nodes) == 2  # C and inner_comp


class TestPathModelFn:
    def test_create_path_model_fn_simple_loop_compute(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_loop("loop1", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]) as loop:
            builder.add_compute("comp1", reads=[(A, i)], writes=[(B, i)])

        path_model_fn = create_path_model_fn(loop)

        k = Symbol("k", INT)
        path_model = path_model_fn(k)

        assert len(path_model) == 1
        predicate, write_set, read_set = path_model[0]

        assert predicate == TRUE()
        assert write_set == [(B.array_id, k)]
        assert read_set == [(A.array_id, k), (B.array_id, k)]

    def test_create_path_model_fn_loop_with_branch(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        x = builder.add_symbol("x")
        A = builder.add_data("A")
        B = builder.add_data("B")
        C = builder.add_data("C")

        with builder.add_loop("loop1", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]) as loop:
            with builder.add_branch("branch1", reads=[], writes=[]) as branch:
                with branch.add_path(GE(x, Int(0))):
                    builder.add_compute("comp_true", reads=[(A, i)], writes=[(B, i)])
                with branch.add_path(LE(x, Int(-1))):
                    builder.add_compute("comp_false", reads=[(A, Plus(i, Int(1)))], writes=[(C, i)])

        path_model_fn = create_path_model_fn(loop)
        k = Symbol("k", INT)
        path_model = path_model_fn(k)

        assert len(path_model) == 2

        # Path 1: GE(x, 0)
        predicate1, write_set1, read_set1 = path_model[0]
        assert simplify(predicate1) == simplify(GE(x, Int(0)))
        assert write_set1 == [(B.array_id, k)]
        assert read_set1 == [(A.array_id, k), (B.array_id, k)]

        # Path 2: LE(x, -1)
        predicate2, write_set2, read_set2 = path_model[1]
        assert simplify(predicate2) == simplify(LE(x, Int(-1)))
        assert write_set2 == [(C.array_id, k)]
        assert read_set2 == [(A.array_id, Plus(k, Int(1))), (C.array_id, k)]

    def test_create_path_model_fn_loop_with_nested_loop(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        j = builder.add_symbol("j")
        N = builder.add_symbol("N")
        M = builder.add_symbol("M")
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_loop("outer_loop", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]) as outer_loop:
            with builder.add_loop("inner_loop", "j", Int(0), M, reads=[(A, j)], writes=[(B, j)]) as inner_loop:
                builder.add_compute("comp_inner", reads=[(A, Plus(i, j))], writes=[(B, Plus(i, j))])

        path_model_fn = create_path_model_fn(outer_loop)
        k_outer = Symbol("k_outer", INT)
        path_model = path_model_fn(k_outer)

        assert len(path_model) == 1
        predicate, write_set, read_set = path_model[0]

        assert predicate == TRUE()
        # The inner loop variable 'j' should not be substituted by 'k_outer'
        assert read_set == [(A.array_id, Plus(k_outer, j)), (B.array_id, Plus(k_outer, j))]

    def test_create_path_model_fn_loop_with_map(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        j = builder.add_symbol("j")
        N = builder.add_symbol("N")
        M = builder.add_symbol("M")
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_loop("outer_loop", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]) as outer_loop:
            with builder.add_map("inner_map", "j", Int(0), M, reads=[(A, j)], writes=[(B, j)]) as inner_map:
                builder.add_compute("comp_inner", reads=[(A, Plus(i, j))], writes=[(B, Plus(i, j))])

            path_model_fn = create_path_model_fn(outer_loop)
            k_outer = Symbol("k_outer", INT)
            path_model = path_model_fn(k_outer)

            assert len(path_model) == 1
            predicate, write_set, read_set = path_model[0]

            assert predicate == TRUE()
            assert write_set == [(B.array_id, Plus(k_outer, j))]
            assert read_set == [(A.array_id, Plus(k_outer, j)), (B.array_id, Plus(k_outer, j))]

    def test_create_path_model_fn_loop_with_reduce(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        j = builder.add_symbol("j")
        N = builder.add_symbol("N")
        M = builder.add_symbol("M")
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_loop("outer_loop", "i", Int(0), N, reads=[(A, i)], writes=[(B, i)]) as outer_loop:
            with builder.add_reduce("inner_reduce", "j", Int(0), M, TRUE(), reads=[(A, j)],
                                    writes=[(B, Int(0))]) as inner_reduce:
                builder.add_compute("comp_inner", reads=[(A, Plus(i, j))], writes=[(B, Plus(i, j))])

        path_model_fn = create_path_model_fn(outer_loop)
        k_outer = Symbol("k_outer", INT)
        path_model = path_model_fn(k_outer)

        assert len(path_model) == 1
        predicate, write_set, read_set = path_model[0]

        assert predicate == TRUE()
        assert read_set == [(A.array_id, Plus(k_outer, j)), (B.array_id, Plus(k_outer, j))]

    def test_recursive_substitute_tuple(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        k = Symbol("k", INT)

        # Test with a tuple of formulas
        formula_tuple = (Plus(i, Int(1)), And(GE(i, Int(0)), LE(i, Int(10))))
        substitution_map = {i: k}

        # Manually call the internal recursive_substitute function
        # This requires accessing the function directly, which is not ideal for external testing.
        # For now, we'll simulate its behavior or refactor if needed.
        # Let's assume create_path_model_fn uses it correctly and test through that.
        # For direct testing, we'd need to extract it or make it public.

        # Since recursive_substitute is an inner function, we'll test its effect via create_path_model_fn
        # Create a dummy loop and a compute node with a tuple subset
        N = builder.add_symbol("N")
        A = builder.add_data("A")
        B = builder.add_data("B")

        with builder.add_loop("loop_tuple", "i", Int(0), N, reads=[(A, (i, Plus(i, Int(1))))],
                              writes=[(B, (i, Plus(i, Int(1))))]) as loop:
            builder.add_compute("comp_tuple", reads=[(A, (i, Plus(i, Int(1))))], writes=[(B, (i, Plus(i, Int(1))))])

        path_model_fn = create_path_model_fn(loop)
        solver_k = Symbol("solver_k", INT)
        path_model = path_model_fn(solver_k)

        assert len(path_model) == 1
        predicate, write_set, read_set = path_model[0]

        assert write_set == [(B.array_id, (solver_k, Plus(solver_k, Int(1))))]
        assert read_set == [(A.array_id, (solver_k, Plus(solver_k, Int(1)))),
                            (B.array_id, (solver_k, Plus(solver_k, Int(1))))]
