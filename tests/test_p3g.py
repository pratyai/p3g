import pytest
from pysmt.shortcuts import (
    Symbol,
    INT,
    TRUE,
    And,
    GE,
    LE,
    Plus,
    Int,
    simplify,
    ArrayType,
    Minus,
    Times,
    reset_env,
    get_env,
)

from p3g.graph import (
    PysmtRange,
    PysmtCoordSet,
    Compute,
    GraphBuilder,
    create_path_model_fn,
    Data,
)
from p3g.inference import InferenceEngine


@pytest.fixture(autouse=True)
def pysmt_env():
    reset_env()
    get_env().enable_infix_notation = True


# Helper function to create a simple PysmtFormula for testing
def create_subset_formula(name: str):
    return Symbol(name, INT)


class TestCompute:
    def test_compute_creation(self):
        compute_node = Compute("C1")
        # Justification: Verify that the name of the Compute node is correctly set during initialization.
        assert compute_node.name == "C1"
        # Justification: Verify that the string representation of the Compute node matches the expected format.
        assert repr(compute_node) == "COMPUTE(C1)"

    def test_get_read_write_set(self):
        builder = GraphBuilder()
        A = builder.add_read_data("A")
        B = builder.add_read_data("B")
        C_in, C_out = builder.add_write_data("C")

        c_node = builder.add_compute(
            "C1",
            reads=[(A, Int(0)), (B, Int(1)), (C_in, Int(2))],
            writes=[(C_out, Int(2))],
        )

        read_set = c_node.get_read_set()
        write_set = c_node.get_write_set()

        # Justification: The read set should include all explicitly read data (A, B)
        # and also the data being written to (C), as writes imply a read-before-write
        # for dependency analysis in some contexts.
        assert len(read_set) == 3
        assert (A.array_id, Int(0)) in read_set
        assert (B.array_id, Int(1)) in read_set
        assert (C_in.array_id, Int(2)) in read_set

        # Justification: The write set should only include the explicitly written data (C).
        assert len(write_set) == 1
        expected_write_set = {(C_out.array_id, Int(2))}
        actual_write_set = {item for item in write_set}
        assert actual_write_set == expected_write_set


class TestGraphBuilder:
    def test_builder_init(self):
        builder = GraphBuilder()
        # Justification: Verify that a root graph is initialized upon builder creation.
        assert builder.root_graph is not None
        # Justification: Verify that the current graph context is initially set to the root graph.
        assert builder.current_graph == builder.root_graph
        # Justification: Verify that the internal counter for data IDs starts at the expected value.
        assert builder._next_data_id == 10001

    def test_add_symbol(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        # Justification: Verify that the symbol is added to the root graph's symbol dictionary.
        assert "i" in builder.root_graph.symbols
        # Justification: Verify that the added symbol object is correctly stored in the root graph.
        assert builder.root_graph.symbols["i"] == i

    def test_add_data(self):
        builder = GraphBuilder()
        A = builder.add_data("A")
        B = builder.add_data("B")

        # Justification: Verify that the name of the data node A is correctly set.
        assert A.name == "A(0)"
        # Justification: Verify that the array_id for data node A is assigned sequentially.
        assert A.array_id == 10001
        # Justification: Verify that data node A is added to the root graph's nodes.
        assert A in builder.root_graph.nodes

        # Justification: Verify that the name of the data node B is correctly set.
        assert B.name == "B(0)"
        # Justification: Verify that the array_id for data node B is assigned sequentially.
        assert B.array_id == 10002
        # Justification: Verify that data node B is added to the root graph's nodes.
        assert B in builder.root_graph.nodes

    def test_add_compute(self):
        builder = GraphBuilder()
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")
        C_in, C_out = builder.add_write_data("C")

        compute_node = builder.add_compute(
            "C1",
            reads=[(A, Int(0)), (B_in, Int(1)), (C_in, Int(2))],
            writes=[(B_out, Int(1)), (C_out, Int(2))],
        )

        # Justification: Verify that the compute node is added to the root graph's nodes.
        assert compute_node in builder.root_graph.nodes
        # Justification: Verify the correct number of incoming edges (reads + writes).
        # Reads: A, B. Writes: C. Total 3.
        assert len(compute_node.in_edges) == 3
        expected_in_edges = {
            (A, compute_node, Int(0)),
            (B_in, compute_node, Int(1)),
            (C_in, compute_node, Int(2)),
        }
        actual_in_edges = {
            (edge.src, edge.dst, edge.subset) for edge in compute_node.in_edges
        }
        # Justification: Verify that the incoming edges correctly represent the reads and writes.
        assert actual_in_edges == expected_in_edges

        # Justification: Verify the correct number of outgoing edges (writes).
        # Writes: B, C. Total 2.
        assert len(compute_node.out_edges) == 2
        expected_out_edges = {
            (compute_node, B_out, Int(1)),
            (compute_node, C_out, Int(2)),
        }
        actual_out_edges = {
            (edge.src, edge.dst, edge.subset) for edge in compute_node.out_edges
        }
        # Justification: Verify that the outgoing edges correctly represent the writes.
        assert actual_out_edges == expected_out_edges

    def test_add_loop(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")

        with builder.add_loop(
            "loop1",
            "i",
            Int(0),
            N,
            reads=[(A, PysmtRange(Int(0), N)), (B_in, PysmtRange(Int(0), N))],
            writes=[(B_out, PysmtRange(Int(0), N))],
        ) as loop:
            # Justification: Verify that the loop variable is correctly set.
            assert loop.loop_var == i
            # Justification: Verify that the loop start bound is correctly set.
            assert loop.start == Int(0)
            # Justification: Verify that the loop end bound is correctly set.
            assert loop.end == N
            # Justification: Verify that the loop node is added to the root graph's nodes.
            assert loop in builder.root_graph.nodes
            # Justification: Verify that the current graph context is switched to the nested graph of the loop.
            assert builder.current_graph == loop.nested_graph

            # Check hierarchical edges
            # Justification: Verify the correct number of incoming hierarchical edges for the loop.
            # Reads: A. Writes: B. Total 2.
            assert len(loop.in_edges) == 2
            expected_in_edges = {(A, loop, (Int(0), N)), (B_in, loop, (Int(0), N))}
            actual_in_edges = {
                (edge.src, edge.dst, edge.subset) for edge in loop.in_edges
            }
            # Justification: Verify that the incoming hierarchical edges correctly represent the reads and writes.
            assert actual_in_edges == expected_in_edges

            # Justification: Verify the correct number of outgoing hierarchical edges for the loop.
            # Writes: B. Total 1.
            assert len(loop.out_edges) == 1
            expected_out_edges = {(loop, B_out, (Int(0), N))}
            actual_out_edges = {
                (edge.src, edge.dst, edge.subset) for edge in loop.out_edges
            }
            # Justification: Verify that the outgoing hierarchical edges correctly represent the writes.
            assert actual_out_edges == expected_out_edges

            C_in, C_out = builder.add_write_data("C")
            builder.add_compute(
                "inner_comp", reads=[(A, i), (C_in, i)], writes=[(C_out, i)]
            )

        # Justification: Verify that the current graph context is restored to the root graph after exiting the loop.
        assert builder.current_graph == builder.root_graph
        # Justification: Verify that the nested graph of the loop contains the newly added data node C and compute node inner_comp.
        assert len(loop.nested_graph.nodes) == 3  # C_in, C_out and inner_comp

    def test_add_map(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")

        with builder.add_map(
            "map1",
            "i",
            Int(0),
            N,
            reads=[(A, PysmtRange(Int(0), N)), (B_in, PysmtRange(Int(0), N))],
            writes=[(B_out, PysmtRange(Int(0), N))],
        ) as map_node:
            # Justification: Verify that the loop variable is correctly set for the map node.
            assert map_node.loop_var == i
            # Justification: Verify that the start bound is correctly set for the map node.
            assert map_node.start == Int(0)
            # Justification: Verify that the end bound is correctly set for the map node.
            assert map_node.end == N
            # Justification: Verify that the map node is added to the root graph's nodes.
            assert map_node in builder.root_graph.nodes
            # Justification: Verify that the current graph context is switched to the nested graph of the map node.
            assert builder.current_graph == map_node.nested_graph

            # Check hierarchical edges
            # Justification: Verify the correct number of incoming hierarchical edges for the map node.
            # Reads: A. Writes: B. Total 2.
            assert len(map_node.in_edges) == 2
            expected_in_edges = {
                (A, map_node, (Int(0), N)),
                (B_in, map_node, (Int(0), N)),
            }
            actual_in_edges = {
                (edge.src, edge.dst, edge.subset) for edge in map_node.in_edges
            }
            # Justification: Verify that the incoming hierarchical edges correctly represent the reads and writes.
            assert actual_in_edges == expected_in_edges

            # Justification: Verify the correct number of outgoing hierarchical edges for the map node.
            # Writes: B. Total 1.
            assert len(map_node.out_edges) == 1
            expected_out_edges = {(map_node, B_out, (Int(0), N))}
            actual_out_edges = {
                (edge.src, edge.dst, edge.subset) for edge in map_node.out_edges
            }
            # Justification: Verify that the outgoing hierarchical edges correctly represent the writes.
            assert actual_out_edges == expected_out_edges

            C_in, C_out = builder.add_write_data("C")
            builder.add_compute(
                "inner_comp", reads=[(A, i), (C_in, i)], writes=[(C_out, i)]
            )

        # Justification: Verify that the current graph context is restored to the root graph after exiting the map block.
        assert builder.current_graph == builder.root_graph
        # Justification: Verify that the nested graph of the map node contains the newly added data node C and compute node inner_comp.
        assert len(map_node.nested_graph.nodes) == 3  # C_in, C_out and inner_comp

    def test_add_branch(self):
        builder = GraphBuilder()
        x = builder.add_symbol("x")
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")

        with builder.add_branch(
            "branch1", reads=[(A, Int(0)), (B_in, Int(0))], writes=[(B_out, Int(0))]
        ) as branch:
            # Justification: Verify that the branch node is added to the root graph's nodes.
            assert branch in builder.root_graph.nodes

            # Check hierarchical edges
            # Justification: Verify the correct number of incoming hierarchical edges for the branch node.
            # Reads: A. Writes: B. Total 2.
            assert len(branch.in_edges) == 2
            expected_in_edges = {(A, branch, Int(0)), (B_in, branch, Int(0))}
            actual_in_edges = {
                (edge.src, edge.dst, edge.subset) for edge in branch.in_edges
            }
            # Justification: Verify that the incoming hierarchical edges correctly represent the reads and writes.
            assert actual_in_edges == expected_in_edges

            # Justification: Verify the correct number of outgoing hierarchical edges for the branch node.
            # Writes: B. Total 1.
            assert len(branch.out_edges) == 1
            expected_out_edges = {(branch, B_out, Int(0))}
            actual_out_edges = {
                (edge.src, edge.dst, edge.subset) for edge in branch.out_edges
            }
            # Justification: Verify that the outgoing hierarchical edges correctly represent the writes.
            assert actual_out_edges == expected_out_edges

            with branch.add_path(GE(x, Int(0))):
                C_in, C_out = builder.add_write_data("C")
                builder.add_compute(
                    "comp_true",
                    reads=[(A, Int(0)), (C_in, Int(0))],
                    writes=[(C_out, Int(0))],
                )

            with branch.add_path(LE(x, Int(-1))):
                D_in, D_out = builder.add_write_data("D")
                builder.add_compute(
                    "comp_false",
                    reads=[(A, Int(0)), (D_in, Int(0))],
                    writes=[(D_out, Int(0))],
                )

        # Justification: Verify that the current graph context is restored to the root graph after exiting the branch block.
        assert builder.current_graph == builder.root_graph
        # Justification: Verify that the branch node correctly stores two paths.
        assert len(branch.branches) == 2
        # Justification: Verify the predicate of the first path.
        assert branch.branches[0][0] == GE(x, Int(0))
        # Justification: Verify the predicate of the second path.
        assert branch.branches[1][0] == LE(x, Int(-1))
        # Justification: Verify that the nested graph of the first path contains the newly added data node C and compute node comp_true.
        assert len(branch.branches[0][1].nodes) == 3  # C_in, C_out and comp_true
        # Justification: Verify that the nested graph of the second path contains the newly added data node D and compute node comp_false.
        assert len(branch.branches[1][1].nodes) == 3  # D_in, D_out and comp_false

    def test_add_reduce(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")

        with builder.add_reduce(
            "reduce1",
            "i",
            Int(0),
            N,
            TRUE(),
            reads=[(A, PysmtRange(Int(0), N)), (B_in, Int(0))],
            writes=[(B_out, Int(0))],
        ) as reduce_node:
            # Justification: Verify that the loop variable is correctly set for the reduce node.
            assert reduce_node.loop_var == i
            # Justification: Verify that the start bound is correctly set for the reduce node.
            assert reduce_node.start == Int(0)
            # Justification: Verify that the end bound is correctly set for the reduce node.
            assert reduce_node.end == N
            # Justification: Verify that the write-conflict-resolution predicate is correctly set.
            assert reduce_node.wcr == TRUE()
            # Justification: Verify that the reduce node is added to the root graph's nodes.
            assert reduce_node in builder.root_graph.nodes
            # Justification: Verify that the current graph context is switched to the nested graph of the reduce node.
            assert builder.current_graph == reduce_node.nested_graph

            # Check hierarchical edges
            # Justification: Verify the correct number of incoming hierarchical edges for the reduce node.
            # Reads: A. Writes: B. Total 2.
            assert len(reduce_node.in_edges) == 2
            expected_in_edges = {
                (A, reduce_node, (Int(0), N)),
                (B_in, reduce_node, Int(0)),
            }
            actual_in_edges = {
                (edge.src, edge.dst, edge.subset) for edge in reduce_node.in_edges
            }
            # Justification: Verify that the incoming hierarchical edges correctly represent the reads and writes.
            assert actual_in_edges == expected_in_edges

            # Justification: Verify the correct number of outgoing hierarchical edges for the reduce node.
            # Writes: B. Total 1.
            assert len(reduce_node.out_edges) == 1
            expected_out_edges = {(reduce_node, B_out, Int(0))}
            actual_out_edges = {
                (edge.src, edge.dst, edge.subset) for edge in reduce_node.out_edges
            }
            # Justification: Verify that the outgoing hierarchical edges correctly represent the writes.
            assert actual_out_edges == expected_out_edges

            C_in, C_out = builder.add_write_data("C")
            builder.add_compute(
                "inner_comp", reads=[(A, i), (C_in, i)], writes=[(C_out, i)]
            )

        # Justification: Verify that the current graph context is restored to the root graph after exiting the reduce block.
        assert builder.current_graph == builder.root_graph
        # Justification: Verify that the nested graph of the reduce node contains the newly added data node C and compute node inner_comp.
        assert len(reduce_node.nested_graph.nodes) == 3  # C_in, C_out and inner_comp


class TestPathModelFn:
    def test_create_path_model_fn_simple_loop_compute(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")

        with builder.add_loop(
            "loop1",
            "i",
            Int(0),
            N,
            reads=[(A, PysmtRange(Int(0), N)), (B_in, PysmtRange(Int(0), N))],
            writes=[(B_out, PysmtRange(Int(0), N))],
        ) as loop:
            builder.add_compute("comp1", reads=[(A, i), (B_in, i)], writes=[(B_out, i)])

        path_model_fn = create_path_model_fn(loop)

        k = Symbol("k", INT)
        path_model = path_model_fn(k)

        # Justification:
        # The `_traverse` function in `p3g.py` is called with `loop.nested_graph`.
        # `loop.nested_graph` contains only the `comp1` node.
        # The `_traverse` function, as currently implemented in `p3g.py`, collects the
        # accesses of the `comp1` node and appends them to `all_paths`.
        # Therefore, `path_model` should contain exactly one entry, corresponding to
        # the accesses of the `comp1` node.
        assert len(path_model) == 1
        predicate, write_set, read_set = path_model[0]

        # Justification:
        # The predicate for this path should be TRUE() as there are no conditional branches.
        assert predicate == TRUE()
        # Justification:
        # The `write_set` should reflect the writes of the `comp1` node.
        # The `comp1`'s writes are `[(B, i)]`.
        # After substituting `i` with `k`, this becomes `[(B.array_id, k)]`.
        assert write_set == [(B_out.array_id, k)]
        # Justification:
        # The `read_set` should reflect the reads of the `comp1` node.
        # The `comp1`'s reads are `[(A, i)]` and its writes are `[(B, i)]`.
        # As per `add_reads_and_writes` in `p3g.py`, writes are also considered reads for dependency analysis.
        # After substituting `i` with `k`, this becomes:
        # `[(A.array_id, k), (B.array_id, k)]`.
        assert read_set == [(A.array_id, k), (B_in.array_id, k)]

    def test_create_path_model_fn_loop_with_branch(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        N = builder.add_symbol("N")
        x = builder.add_symbol("x")
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")
        C_in, C_out = builder.add_write_data("C")

        with builder.add_loop(
            "loop1",
            "i",
            Int(0),
            N,
            reads=[
                (A, PysmtRange(Int(0), N)),
                (B_in, PysmtRange(Int(0), N)),
                (C_in, PysmtRange(Int(0), N)),
            ],
            writes=[(B_out, PysmtRange(Int(0), N)), (C_out, PysmtRange(Int(0), N))],
        ) as loop:
            with builder.add_branch("branch1", reads=[], writes=[]) as branch:
                with branch.add_path(GE(x, Int(0))):
                    builder.add_compute(
                        "comp_true", reads=[(A, i), (B_in, i)], writes=[(B_out, i)]
                    )
                with branch.add_path(LE(x, Int(-1))):
                    builder.add_compute(
                        "comp_false",
                        reads=[(A, Plus(i, Int(1))), (C_in, i)],
                        writes=[(C_out, i)],
                    )

        path_model_fn = create_path_model_fn(loop)
        k = Symbol("k", INT)
        path_model = path_model_fn(k)

        # Justification:
        # The `_traverse` function in `p3g.py` is called with `loop.nested_graph`.
        # `loop.nested_graph` contains only the `branch1` node.
        # The `_traverse` function, as currently implemented in `p3g.py`, recursively
        # traverses the branches of `branch1`. Each path within the branch generates
        # a separate entry in `path_model`. Since there are two paths, `path_model`
        # should contain two entries.
        assert len(path_model) == 2

        # Path 1: GE(x, 0)
        predicate1, write_set1, read_set1 = path_model[0]
        # Justification: The predicate for this path is GE(x, 0).
        assert simplify(predicate1) == simplify(GE(x, Int(0)))
        # Justification: The `write_set` for this path comes from `comp_true`'s writes.
        # `comp_true` writes `[(B, i)]`. After substituting `i` with `k`, this becomes `[(B.array_id, k)]`.
        assert write_set1 == [(B_out.array_id, k)]
        # Justification: The `read_set` for this path comes from `comp_true`'s reads and writes.
        # `comp_true` reads `[(A, i)]` and writes `[(B, i)]`. After substituting `i` with `k`, this becomes `[(A.array_id, k), (B.array_id, k)]`.
        assert read_set1 == [(A.array_id, k), (B_in.array_id, k)]

        # Path 2: LE(x, -1)
        predicate2, write_set2, read_set2 = path_model[1]
        # Justification: The predicate for this path is LE(x, -1).
        assert simplify(predicate2) == simplify(LE(x, Int(-1)))
        # Justification: The `write_set` for this path comes from `comp_false`'s writes.
        # `comp_false` writes `[(C, i)]`. After substituting `i` with `k`, this becomes `[(C.array_id, k)]`.
        assert write_set2 == [(C_out.array_id, k)]
        # Justification: The `read_set` for this path comes from `comp_false`'s reads and writes.
        # `comp_false` reads `[(A, Plus(i, Int(1)))]` and writes `[(C, i)]`. After substituting `i` with `k`, this becomes `[(A.array_id, Plus(k, Int(1))), (C.array_id, k)]`.
        assert read_set2 == [(A.array_id, Plus(k, Int(1))), (C_in.array_id, k)]

    def test_create_path_model_fn_loop_with_nested_loop(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        j = builder.add_symbol("j")
        N = builder.add_symbol("N")
        M = builder.add_symbol("M")
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")

        with builder.add_loop(
            "outer_loop",
            "i",
            Int(0),
            N,
            reads=[(A, PysmtRange(Int(0), N + M)), (B_in, PysmtRange(Int(0), N + M))],
            writes=[(B_out, PysmtRange(Int(0), N + M))],
        ) as outer_loop:
            with builder.add_loop(
                "inner_loop",
                "j",
                Int(0),
                M,
                reads=[
                    (A, PysmtRange(Plus(i, Int(0)), Plus(i, M))),
                    (B_in, PysmtRange(Plus(i, Int(0)), Plus(i, M))),
                ],
                writes=[(B_out, PysmtRange(Plus(i, Int(0)), Plus(i, M)))],
            ) as inner_loop:
                builder.add_compute(
                    "comp_inner",
                    reads=[(A, Plus(i, j)), (B_in, Plus(i, j))],
                    writes=[(B_out, Plus(i, j))],
                )

        path_model_fn = create_path_model_fn(outer_loop)
        k_outer = Symbol("k_outer", INT)
        path_model = path_model_fn(k_outer)

        # Justification:
        # The `_traverse` function in `p3g.py` is called with `outer_loop.nested_graph`.
        # `outer_loop.nested_graph` contains only the `inner_loop` node.
        # The `_traverse` function, as currently implemented in `p3g.py`, collects the
        # hierarchical edges of the `inner_loop` node and appends them to `all_paths`.
        # It does NOT collect the hierarchical edges of the `outer_loop` itself,
        # as they are part of the `outer_loop` node, not its `nested_graph`.
        # Therefore, `path_model` should contain exactly one entry, corresponding to
        # the hierarchical edges of the `inner_loop`.
        assert len(path_model) == 1

        predicate, write_set, read_set = path_model[0]

        # Justification:
        # The predicate for this path should be TRUE() as there are no conditional branches.
        assert predicate == TRUE()

        # Justification:
        # The `write_set` should reflect the hierarchical writes of the `inner_loop`.
        # The `inner_loop`'s writes are `[(B, (Plus(i, Int(0)), Plus(i, M)))]`.
        # After substituting `i` with `k_outer`, this becomes `[(B.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M)))]`.
        assert write_set == [
            (B_out.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M)))
        ]

        # Justification:
        # The `read_set` should reflect the hierarchical reads of the `inner_loop`.
        # The `inner_loop`'s reads are `[(A, (Plus(i, Int(0)), Plus(i, M)))]` and
        # its writes are `[(B, (Plus(i, Int(0)), Plus(i, M)))]`.
        # As per `add_reads_and_writes` in `p3g.py`, writes are also considered reads for dependency analysis.
        # After substituting `i` with `k_outer`, this becomes:
        # `[(A.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M))), (B.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M)))]`.
        assert read_set == [
            (A.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M))),
            (B_in.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M))),
        ]

    def test_create_path_model_fn_loop_with_map(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        j = builder.add_symbol("j")
        N = builder.add_symbol("N")
        M = builder.add_symbol("M")
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")

        with builder.add_loop(
            "outer_loop",
            "i",
            Int(0),
            N,
            reads=[(A, PysmtRange(Int(0), N)), (B_in, PysmtRange(Int(0), N))],
            writes=[(B_out, PysmtRange(Int(0), N))],
        ) as outer_loop:
            with builder.add_map(
                "inner_map",
                "j",
                Int(0),
                M,
                reads=[
                    (A, PysmtRange(Plus(i, Int(0)), Plus(i, M))),
                    (B_in, PysmtRange(Plus(i, Int(0)), Plus(i, M))),
                ],
                writes=[(B_out, PysmtRange(Plus(i, Int(0)), Plus(i, M)))],
            ) as inner_map:
                builder.add_compute(
                    "comp_inner",
                    reads=[(A, Plus(i, j)), (B_in, Plus(i, j))],
                    writes=[(B_out, Plus(i, j))],
                )

            path_model_fn = create_path_model_fn(outer_loop)
            k_outer = Symbol("k_outer", INT)
            path_model = path_model_fn(k_outer)

            # Justification:
            # The `_traverse` function in `p3g.py` is called with `outer_loop.nested_graph`.
            # `outer_loop.nested_graph` contains only the `inner_map` node.
            # The `_traverse` function, as currently implemented in `p3g.py`, collects the
            # hierarchical edges of the `inner_map` node and appends them to `all_paths`.
            # It does NOT collect the hierarchical edges of the `outer_loop` itself,
            # as they are part of the `outer_loop` node, not its `nested_graph`.
            # Therefore, `path_model` should contain exactly one entry, corresponding to
            # the hierarchical edges of the `inner_map`.
            assert len(path_model) == 1

            predicate, write_set, read_set = path_model[0]

            # Justification:
            # The predicate for this path should be TRUE() as there are no conditional branches.
            assert predicate == TRUE()

            # Justification:
            # The `write_set` should reflect the hierarchical writes of the `inner_map`.
            # The `inner_map`'s writes are `[(B, (Plus(i, Int(0)), Plus(i, M)))]`.
            # After substituting `i` with `k_outer`, this becomes `[(B.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M)))]`.
            assert write_set == [
                (B_out.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M)))
            ]

            # Justification:
            # The `read_set` should reflect the hierarchical reads of the `inner_map`.
            # The `inner_map`'s reads are `[(A, (Plus(i, Int(0)), Plus(i, M)))]` and
            # its writes are `[(B, (Plus(i, Int(0)), Plus(i, M)))]`.
            # As per `add_reads_and_writes` in `p3g.py`, writes are also considered reads for dependency analysis.
            # After substituting `i` with `k_outer`, this becomes:
            # `[(A.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M))), (B.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M)))]`.
            assert read_set == [
                (A.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M))),
                (B_in.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M))),
            ]

    def test_create_path_model_fn_loop_with_reduce(self):
        builder = GraphBuilder()
        i = builder.add_symbol("i")
        j = builder.add_symbol("j")
        N = builder.add_symbol("N")
        M = builder.add_symbol("M")
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")

        with builder.add_loop(
            "outer_loop",
            "i",
            Int(0),
            N,
            reads=[(A, PysmtRange(Int(0), N)), (B_in, PysmtRange(Int(0), N))],
            writes=[(B_out, PysmtRange(Int(0), N))],
        ) as outer_loop:
            with builder.add_reduce(
                "inner_reduce",
                "j",
                Int(0),
                M,
                TRUE(),
                reads=[(A, PysmtRange(Plus(i, Int(0)), Plus(i, M))), (B_in, Int(0))],
                writes=[(B_out, Int(0))],
            ) as inner_reduce:
                builder.add_compute(
                    "comp_inner",
                    reads=[(A, Plus(i, j)), (B_in, Plus(i, j))],
                    writes=[(B_out, Plus(i, j))],
                )

        path_model_fn = create_path_model_fn(outer_loop)
        k_outer = Symbol("k_outer", INT)
        path_model = path_model_fn(k_outer)

        # Justification:
        # The `_traverse` function in `p3g.py` is called with `outer_loop.nested_graph`.
        # `outer_loop.nested_graph` contains only the `inner_reduce` node.
        # The `_traverse` function, as currently implemented in `p3g.py`, collects the
        # hierarchical edges of the `inner_reduce` node and appends them to `all_paths`.
        # It does NOT collect the hierarchical edges of the `outer_loop` itself,
        # as they are part of the `outer_loop` node, not its `nested_graph`.
        # Therefore, `path_model` should contain exactly one entry, corresponding to
        # the hierarchical edges of the `inner_reduce`.
        assert len(path_model) == 1

        predicate, write_set, read_set = path_model[0]

        # Justification:
        # The predicate for this path should be TRUE() as there are no conditional branches.
        assert predicate == TRUE()

        # Justification:
        # The `write_set` should reflect the hierarchical writes of the `inner_reduce`.
        # The `inner_reduce`'s writes are `[(B, Int(0))]`.
        # After substituting `i` with `k_outer`, this remains `[(B.array_id, Int(0))]`.
        assert write_set == [(B_out.array_id, Int(0))]

        # Justification:
        # The `read_set` should reflect the hierarchical reads of the `inner_reduce`.
        # The `inner_reduce`'s reads are `[(A, (Plus(i, Int(0)), Plus(i, M)))]` and
        # its writes are `[(B, Int(0))]`.
        # As per `add_reads_and_writes` in `p3g.py`, writes are also considered reads for dependency analysis.
        # After substituting `i` with `k_outer`, this becomes:
        # `[(A.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M))), (B.array_id, Int(0))]`.
        assert read_set == [
            (A.array_id, (Plus(k_outer, Int(0)), Plus(k_outer, M))),
            (B_in.array_id, Int(0)),
        ]

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
        A = builder.add_read_data("A")
        B_in, B_out = builder.add_write_data("B")

        with builder.add_loop(
            "loop_tuple",
            "i",
            Int(0),
            N,
            reads=[
                (A, PysmtCoordSet(PysmtRange(Int(0), N), PysmtRange(Int(0), N))),
                (B_in, PysmtCoordSet(PysmtRange(Int(0), N), PysmtRange(Int(0), N))),
            ],
            writes=[
                (B_out, PysmtCoordSet(PysmtRange(Int(0), N), PysmtRange(Int(0), N)))
            ],
        ) as loop:
            builder.add_compute(
                "comp_tuple",
                reads=[
                    (A, PysmtRange(i, Plus(i, Int(1)))),
                    (B_in, PysmtRange(i, Plus(i, Int(1)))),
                ],
                writes=[(B_out, PysmtRange(i, Plus(i, Int(1))))],
            )

        path_model_fn = create_path_model_fn(loop)
        solver_k = Symbol("solver_k", INT)
        path_model = path_model_fn(solver_k)

        # Justification:
        # The `_traverse` function in `p3g.py` is called with `loop.nested_graph`.
        # `loop.nested_graph` contains only the `comp_tuple` node.
        # The `_traverse` function, as currently implemented in `p3g.py`, collects the
        # accesses of the `comp_tuple` node and appends them to `all_paths`.
        # Therefore, `path_model` should contain exactly one entry, corresponding to
        # the accesses of the `comp_tuple` node.
        assert len(path_model) == 1
        predicate, write_set, read_set = path_model[0]

        # Justification:
        # The `write_set` should reflect the writes of the `comp_tuple` node.
        # The `comp_tuple`'s writes are `[(B, (i, Plus(i, Int(1))))]`.
        # After substituting `i` with `solver_k`, this becomes `[(B.array_id, (solver_k, Plus(solver_k, Int(1))))]`.
        assert write_set == [(B_out.array_id, (solver_k, Plus(solver_k, Int(1))))]
        # Justification:
        # The `read_set` should reflect the reads of the `comp_tuple` node.
        # The `comp_tuple`'s reads are `[(A, (i, Plus(i, Int(1))))]` and its writes are `[(B, (i, Plus(i, Int(1))))]`.
        # As per `add_reads_and_writes` in `p3g.py`, writes are also considered reads for dependency analysis.
        # After substituting `i` with `solver_k`, this becomes:
        # `[(A.array_id, (solver_k, Plus(solver_k, Int(1)))), (B.array_id, (solver_k, Plus(solver_k, Int(1))))]`.
        assert read_set == [
            (A.array_id, (solver_k, Plus(solver_k, Int(1)))),
            (B_in.array_id, (solver_k, Plus(solver_k, Int(1)))),
        ]
