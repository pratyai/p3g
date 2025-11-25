from __future__ import annotations

from collections.abc import Callable

from pysmt.shortcuts import (
    Symbol,
    INT,
    And,
    TRUE,
    substitute,
    Or,
)

from p3g.subsets import (
    PysmtFormula,
    WriteSet,
    ReadSet,
    PysmtRange,
    PysmtCoordSet,
    PysmtSetMembershipPredicate,
    PysmtAccessSubset,
    _custom_simplify_formula,
    PysmtSymbol,
)

PathModel = list[tuple[PysmtFormula, WriteSet, ReadSet]]
PysmtContext = object  # Placeholder for pysmt.shortcuts.Context


# Define __all__ for 'from p3g import *'
__all__ = [
    "Node",
    "Edge",
    "Graph",
    "Data",
    "Compute",
    "Structure",
    "Map",
    "Loop",
    "Branch",
    "Reduce",
    "GraphBuilder",
    "PathContext",
    "create_path_model_fn",
    "PathModel",
]


# --- Base Graph Components ---


class Node:
    """
    Base class for all nodes in the P3G.
    Represents V_D, V_C, and V_S.
    """

    def __init__(
        self,
        name: str,
        graph: "Graph" | None = None,
        parent: "Node" | None = None,
    ):
        self.name = name
        self.graph = graph  # Reference to the graph this node belongs to
        self.parent = parent  # Reference to the immediate parent node in the hierarchy
        self.in_edges: list["Edge"] = []
        self.out_edges: list["Edge"] = []

    def __repr__(self):
        return f"NODE[{self.__class__.__name__}({self.name})]"


class Edge:
    """
    Represents a dataflow edge (E) in the P3G.
    It carries a symbolic subset annotation (a pysmt formula, a range tuple, or None if to be inferred).
    """

    def __init__(
        self,
        src: Node,
        dst: Node,
        subset: PysmtAccessSubset | None,
    ):
        self.src = src
        self.dst = dst
        self.subset = subset

        assert subset is None or isinstance(subset, PysmtAccessSubset), (
            f"Subset ({type(subset)}) must be a PysmtFormula, PysmtRange, PysmtCoordSet, PysmtSetMembershipPredicate object, or None."
        )
        if isinstance(subset, PysmtFormula) and subset.is_store():
            assert False, (
                f"ERROR: Store operation '{subset}' found in Edge subset. "
                "For dependency analysis, edges should specify the memory location "
                "(e.g., Select(array, index)), not the Store operation itself."
            )

        src.out_edges.append(self)
        dst.in_edges.append(self)

    def __repr__(self):
        return f"Edge({self.src.name} -> {self.dst.name} [{self.subset}])"


class Graph:
    """
    Represents a P3G, G = (V, E, Sigma, Omega).
    This can be a top-level graph or a nested graph inside a
    structure node.
    """

    def __init__(self, name: str = "P3G"):
        self.name = name
        self.nodes: list[Node] = []
        self.edges: list[Edge] = []
        self.symbols: dict[str, PysmtSymbol] = {}
        self.outputs: set[int] = set()
        self.transients: set[int] = set()
        self._array_id_to_name: dict[int, str] = {}
        self.assertions: list[PysmtFormula] = []

    def add_node(self, node: Node):
        """
        Adds a node to this graph.

        Args:
            node: The Node instance to add.
        """
        self.nodes.append(node)

    def add_edge(
        self,
        src: Node,
        dst: Node,
        subset: PysmtAccessSubset | None,
    ) -> Edge:
        """
        Adds an edge between two nodes in the graph.

        Args:
            src: The source node of the edge.
            dst: The destination node of the edge.
            subset: The symbolic subset annotation of the edge, or None if to be inferred.

        Returns:
            The created Edge instance.
        """
        edge = Edge(src, dst, subset)
        self.edges.append(edge)
        return edge

    def add_symbol(self, name: str, type=INT):
        sym = Symbol(name, type)
        self.symbols[name] = sym
        return sym


# --- Atomic Nodes (V_D, V_C) ---


class Data(Node):
    """
    A data container node (V_D).
    This represents a *reference* to an array or scalar in memory.
    """

    def __init__(
        self,
        name: str,
        array_id: int,
        graph: "Graph" | None = None,
        parent: "Node" | None = None,
    ):
        super().__init__(name, graph=graph, parent=parent)
        self.array_id = array_id

    def __repr__(self):
        return f"DATA[{self.name}/{self.array_id}]"


class Compute(Node):
    """
    A computation node (V_C).
    Its data accesses are defined *by its incident edges*.
    """

    def __init__(
        self,
        name: str,
        graph: "Graph" | None = None,
        parent: "Node" | None = None,
    ):
        super().__init__(name, graph=graph, parent=parent)

    def __repr__(self):
        return f"COMPUTE({self.name})"

    def get_read_set(self) -> ReadSet:
        """
        Generates the ReadSet by inspecting incoming edges from Data nodes.
        """
        read_set = []
        for edge in self.in_edges:
            if (
                isinstance(edge.src, Data)
                and edge.src.array_id not in self.graph.transients
            ):
                read_set.append((edge.src.array_id, edge.subset))
        return read_set

    def get_write_set(self) -> WriteSet:
        """
        Generates the WriteSet by inspecting outgoing edges to Data nodes.
        """
        write_set = []
        for edge in self.out_edges:
            if (
                isinstance(edge.dst, Data)
                and edge.dst.array_id not in self.graph.transients
            ):
                write_set.append((edge.dst.array_id, edge.subset))
        return write_set


# --- Structure Nodes (V_S) ---


class Structure(Node):
    """
    Base class for hierarchical structure nodes (V_S).
    """

    def __init__(
        self,
        name: str,
        builder: "GraphBuilder",
        graph: "Graph" | None = None,
        parent: "Node" | None = None,
    ):
        super().__init__(name, graph=graph, parent=parent)
        self.builder = builder

    def __repr__(self):
        return f"STRUCTURE({self.name})"


class Map(Structure):
    """
    Represents a parallel Map node in the Program Dependence Graph (P3G).

    A Map node signifies a parallel loop construct where iterations are independent
    and can theoretically be executed concurrently. It encapsulates a nested graph
    representing the body of the loop.

    Attributes:
        loop_var (PysmtSymbol): The symbolic loop variable for this Map.
        start (PysmtFormula): A Pysmt formula representing the inclusive start bound of the loop.
        end (PysmtFormula): A Pysmt formula representing the inclusive end bound of the loop.
        nested_graph (Graph): The graph representing the operations within the Map's body.
    """

    def __init__(
        self,
        name: str,
        builder: "GraphBuilder",
        loop_var_name: str,
        start: PysmtFormula,
        end: PysmtFormula,
        graph: "Graph" | None = None,
        parent: "Node" | None = None,
    ):
        super().__init__(name, builder, graph=graph, parent=parent)
        self.loop_var = Symbol(loop_var_name, INT)
        self.start = start
        self.end = end
        self.nested_graph = Graph(f"{name}_body")

    def __enter__(self):
        self.builder.graph_stack.append(
            (self.nested_graph, self)
        )  # Push (graph, self as owner)
        return self  # Return self so user can access loop_var

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.builder.graph_stack.pop()

    def __repr__(self):
        return f"MAP({self.name}): iter={self.loop_var} in [{self.start}, {self.end}]"

    def get_read_set(self) -> ReadSet:
        """
        Generates the ReadSet by inspecting incoming edges from Data nodes.
        """
        read_set = []
        for edge in self.in_edges:
            if (
                isinstance(edge.src, Data)
                and edge.src.array_id not in self.graph.transients
            ):
                read_set.append((edge.src.array_id, edge.subset))
        return read_set

    def get_write_set(self) -> WriteSet:
        """
        Generates the WriteSet by inspecting outgoing edges to Data nodes.
        """
        write_set = []
        for edge in self.out_edges:
            if (
                isinstance(edge.dst, Data)
                and edge.dst.array_id not in self.graph.transients
            ):
                write_set.append((edge.dst.array_id, edge.subset))
        return write_set


class Loop(Structure):
    """
    Represents a sequential Loop node in the Program Dependence Graph (P3G).

    A Loop node signifies a sequential loop construct where iterations may have
    dependencies on previous iterations. It encapsulates a nested graph
    representing the body of the loop.

    Attributes:
        loop_var (PysmtSymbol): The symbolic loop variable for this Loop.
        start (PysmtFormula): A Pysmt formula representing the inclusive start bound of the loop.
        end (PysmtFormula): A Pysmt formula representing the inclusive end bound of the loop.
        nested_graph (Graph): The graph representing the operations within the Loop's body.
    """

    def __init__(
        self,
        name: str,
        builder: "GraphBuilder",
        loop_var_name: str,
        start: PysmtFormula,
        end: PysmtFormula,
        graph: "Graph" | None = None,
        parent: "Node" | None = None,
    ):
        super().__init__(name, builder, graph=graph, parent=parent)
        self.loop_var = Symbol(loop_var_name, INT)
        self.start = start
        self.end = end
        self.nested_graph = Graph(f"{name}_body")

    def __enter__(self):
        self.builder.graph_stack.append(
            (self.nested_graph, self)
        )  # Push (graph, self as owner)
        return self  # Return self so user can access loop_var

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.builder.graph_stack.pop()

    def __repr__(self):
        return f"LOOP({self.name}): iter={self.loop_var} in [{self.start}, {self.end}]"

    def get_read_set(self) -> ReadSet:
        """
        Generates the ReadSet by inspecting incoming edges from Data nodes.
        """
        read_set = []
        for edge in self.in_edges:
            if (
                isinstance(edge.src, Data)
                and edge.src.array_id not in self.graph.transients
            ):
                read_set.append((edge.src.array_id, edge.subset))
        return read_set

    def get_write_set(self) -> WriteSet:
        """
        Generates the WriteSet by inspecting outgoing edges to Data nodes.
        """
        write_set = []
        for edge in self.out_edges:
            if (
                isinstance(edge.dst, Data)
                and edge.dst.array_id not in self.graph.transients
            ):
                write_set.append((edge.dst.array_id, edge.subset))
        return write_set


class Branch(Structure):
    """
    Represents a Branch node in the Program Dependence Graph (P3G).

    A Branch node signifies a conditional control flow structure (e.g., an if-else statement,
    switch statement). It contains multiple conditional paths, each with a predicate
    and a nested graph representing the operations within that path.

    Attributes:
        branches (List[Tuple[PysmtFormula, Graph]]): A list of tuples, where each tuple
            contains a Pysmt formula representing the predicate for a branch path
            and the nested Graph associated with that path.
    """

    def __init__(
        self,
        name: str,
        builder: "GraphBuilder",
        graph: "Graph" | None = None,
        parent: "Node" | None = None,
    ):
        super().__init__(name, builder, graph=graph, parent=parent)
        self.branches: list[tuple[PysmtFormula, Graph]] = []

    def add_path(self, predicate: PysmtFormula) -> "PathContext":
        """Adds a new conditional path and returns its context."""
        path_graph = Graph(f"{self.name}_branch_{len(self.branches)}")
        self.branches.append((predicate, path_graph))
        return PathContext(self.builder, path_graph, parent=self)  # Pass self as parent

    def __enter__(self):
        """Allows 'with b.add_branch(...) as branch:' syntax."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """No action needed on exit."""
        pass

    def __repr__(self):
        return f"BRANCH({self.name})"

    def get_read_set(self) -> ReadSet:
        """
        Generates the ReadSet by inspecting incoming edges from Data nodes.
        """
        read_set = []
        for edge in self.in_edges:
            if (
                isinstance(edge.src, Data)
                and edge.src.array_id not in self.graph.transients
            ):
                read_set.append((edge.src.array_id, edge.subset))
        return read_set

    def get_write_set(self) -> WriteSet:
        """
        Generates the WriteSet by inspecting outgoing edges to Data nodes.
        """
        write_set = []
        for edge in self.out_edges:
            if (
                isinstance(edge.dst, Data)
                and edge.dst.array_id not in self.graph.transients
            ):
                write_set.append((edge.dst.array_id, edge.subset))
        return write_set

    def get_predicate_read_set(self) -> ReadSet:
        """
        Extracts the ReadSet from the predicates of this Branch node.
        """
        all_predicate_reads: ReadSet = []
        for predicate, _ in self.branches:
            all_predicate_reads.extend(
                _extract_reads_from_formula(predicate, self.builder)
            )
        return all_predicate_reads


class Reduce(Structure):
    """
    Represents a parallel Reduce node in the Program Dependence Graph (P3G).

    A Reduce node signifies a parallel reduction operation (e.g., sum, min, max across an array).
    It processes data in parallel and combines results using a specified reduction operation
    (Write-Conflict Resolution - WCR). It encapsulates a nested graph representing the body
    of the reduction.

    Attributes:
        loop_var (PysmtSymbol): The symbolic loop variable for this Reduce.
        start (PysmtFormula): A Pysmt formula representing the inclusive start bound of the reduction.
        end (PysmtFormula): A Pysmt formula representing the inclusive end bound of the reduction.
        wcr (PysmtFormula): A Pysmt formula defining the Write-Conflict Resolution strategy.
                            This specifies how concurrent writes to the reduction variable are combined.
        nested_graph (Graph): The graph representing the operations within the Reduce's body.
    """

    def __init__(
        self,
        name: str,
        builder: "GraphBuilder",
        loop_var_name: str,
        start: PysmtFormula,
        end: PysmtFormula,
        wcr: PysmtFormula,
        graph: "Graph" | None = None,
        parent: "Node" | None = None,
    ):
        super().__init__(name, builder, graph=graph, parent=parent)
        self.loop_var = Symbol(loop_var_name, INT)
        self.start = start
        self.end = end
        self.wcr = wcr
        self.nested_graph = Graph(f"{name}_body")

    def __enter__(self):
        self.builder.graph_stack.append(
            (self.nested_graph, self)
        )  # Push (graph, self as owner)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.builder.graph_stack.pop()

    def __repr__(self):
        return (
            f"REDUCE({self.name}): iter={self.loop_var} in [{self.start}, {self.end}]"
        )

    def get_read_set(self) -> ReadSet:
        """
        Generates the ReadSet by inspecting incoming edges from Data nodes.
        """
        read_set = []
        for edge in self.in_edges:
            if isinstance(edge.src, Data):
                read_set.append((edge.src.array_id, edge.subset))
        return read_set

    def get_write_set(self) -> WriteSet:
        """
        Generates the WriteSet by inspecting outgoing edges to Data nodes.
        """
        write_set = []
        for edge in self.out_edges:
            if isinstance(edge.dst, Data):
                write_set.append((edge.dst.array_id, edge.subset))
        return write_set


# --- Context Manager for Branch Paths ---


class PathContext:
    """A helper context manager for a single branch path."""

    def __init__(
        self, builder: "GraphBuilder", graph: Graph, parent: "Branch"
    ):  # PathContext parent is the Branch node
        self.builder = builder
        self.graph = graph
        self.parent = parent  # Store reference to the Branch node

    def __enter__(self):
        self.builder.graph_stack.append(
            (self.graph, self.parent)
        )  # Push (graph, parent as owner)

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.builder.graph_stack.pop()


# --- The Builder Class ---


class GraphBuilder:
    """
    Constructs a Program Dependence Graph (P3G) using a recursive builder pattern
    with context managers. It manages the graph hierarchy, assigns unique IDs to
    data containers, and facilitates the addition of nodes and edges.

    The builder maintains a `graph_stack` to keep track of the current graph
    context and its owning node, enabling the creation of nested graphs within
    structure nodes (e.g., Loop, Map, Branch).

    Attributes:
        root_graph (Graph): The top-level graph of the P3G.
        graph_stack (List[Tuple[Graph, Optional[Node]]]): A stack of (graph, owner_node)
                                                         tuples representing the current
                                                         graph hierarchy.
        _data_id_map (Dict[str, int]): Maps data container names (e.g., "A") to
                                       unique integer IDs.
        _next_data_id (int): The next available unique ID for a data container.
        _pysmt_array_sym_to_array_id (Dict[PysmtSymbol, int]): Maps PySMT array symbols
                                                               to their corresponding
                                                               internal `array_id`s.
        _data_node_name_counters (Dict[str, int]): Counters for generating unique
                                                   Data node names (e.g., "A(0)", "A(1)").
        _is_output_arrays (Set[int]): A set of `array_id`s marked as outputs of the
                                      overall graph.
    """

    def __init__(self):
        self.root_graph = Graph("root")
        self.graph_stack: list[tuple[Graph, Node | None]] = [
            (self.root_graph, None)
        ]  # Store (graph, owner_node)

        self._data_id_map: dict[str, int] = {}
        self._next_data_id: int = 10001
        self._pysmt_array_sym_to_array_id: dict[PysmtSymbol, int] = {}
        self._data_node_name_counters: dict[str, int] = {}
        self._is_output_arrays: set[int] = set()
        self._is_transient_arrays: set[int] = set()

    def _get_current_owner_node(self) -> Node | None:
        """
        Returns the owner node of the graph context currently at the top of the stack.
        This node typically represents the structural element (e.g., Loop, Branch)
        that "owns" the `current_graph`.
        """
        return self.graph_stack[-1][1]

    def _get_data_id(self, name: str) -> int:
        """
        Gets or creates a unique integer ID for a data container,
        representing the underlying storage.
        """
        if name not in self._data_id_map:
            self._data_id_map[name] = self._next_data_id
            self._next_data_id += 1
        return self._data_id_map[name]

    @property
    def current_graph(self) -> Graph:
        """
        Returns the graph instance currently at the top of the stack.
        This is the graph to which new nodes and edges will be added
        by default.
        """
        return self.graph_stack[-1][0]  # Return only the graph

    def add_symbol(self, name: str, type=INT) -> PysmtSymbol:
        """Adds a symbol to the root graph."""
        return self.root_graph.add_symbol(name, type)

    def add_assertion(self, assertion: PysmtFormula):
        """Adds an assertion to the current graph."""
        self.current_graph.assertions.append(assertion)

    def mark_array_as_output(self, name: str):
        """
        Marks an array as an output of the overall graph.
        This should be called during the parsing of 'out' statements.
        """
        array_id = self._get_data_id(name)
        self._is_output_arrays.add(array_id)

    def mark_array_as_transient(self, name: str):
        """
        Marks an array as a transient of the overall graph.
        This should be called during the parsing of 'out' statements.
        """
        array_id = self._get_data_id(name)
        self._is_transient_arrays.add(array_id)

    def add_data(
        self,
        name: str,
        pysmt_array_sym: PysmtSymbol | None = None,
    ) -> Data:
        """
        Adds a Data node to the *current* graph. This node represents a
        local reference to a named data container (e.g., an array or scalar).
        Each call generates a new, unique Data node object (e.g., A(0), A(1))
        even if referring to the same underlying array, to model distinct data states.

        Args:
            name: A string identifier for the underlying data container (e.g., "A", "temp_scalar").
                  This name is used to derive a unique `array_id`.
            pysmt_array_sym: An optional PysmtSymbol representing the array itself
                             (e.g., `Symbol("A_val", ArrayType(INT, INT))`). If provided,
                             this symbol is mapped to the internal `array_id`, which is
                             crucial for `_extract_reads_from_formula` to correctly
                             associate symbolic array accesses (like `Select(A_val, i)`)
                             with their corresponding `array_id` for SMT generation.

        Returns:
            A Data node representing a local reference to the named data container.
        """
        array_id = self._get_data_id(name)

        # Generate a unique name for this Data node object
        self._data_node_name_counters.setdefault(name, -1)
        self._data_node_name_counters[name] += 1
        counter = self._data_node_name_counters[name]

        current_owner_node = self._get_current_owner_node()
        data_node = Data(
            f"{name}({counter})",
            array_id,
            graph=self.current_graph,
            parent=current_owner_node,
        )
        self.current_graph.add_node(data_node)

        # Store array_id to original name mapping in the current graph
        self.current_graph._array_id_to_name[array_id] = name

        if pysmt_array_sym:
            self._pysmt_array_sym_to_array_id[pysmt_array_sym] = array_id

        return data_node

    def add_read_data(
        self, name: str, pysmt_array_sym: PysmtSymbol | None = None
    ) -> Data:
        """
        Adds a Data node to the *current* graph, specifically intended for read operations.
        This is a convenience wrapper around `add_data`.

        Args:
            name: The name of the data container (e.g., "A" for array A).
            pysmt_array_sym: An optional PysmtSymbol representing the array content,
                             used for mapping to the internal array_id.

        Returns:
            A Data node representing a local reference to the named data container.
        """
        return self.add_data(name, pysmt_array_sym)

    def add_write_data(
        self, name: str, pysmt_array_sym: PysmtSymbol | None = None
    ) -> tuple[Data, Data]:
        """
        Adds two Data nodes to the *current* graph, specifically intended for
        explicitly separating read-before-write (input) and write (output) operations
        on the same data container within a scope.

        Both returned Data nodes refer to the same underlying data container (same array_id).
        The first Data node in the tuple is typically used for reads (input),
        and the second for writes (output).

        Args:
            name: The name of the data container (e.g., "A" for array A).
            pysmt_array_sym: An optional PysmtSymbol representing the array content,
                             used for mapping to the internal array_id.

        Returns:
            A tuple containing two Data nodes: (input_data_node, output_data_node).
        """
        return self.add_data(name, pysmt_array_sym), self.add_data(
            name, pysmt_array_sym
        )

    def add_edge(
        self,
        src: Node,
        dst: Node,
        subset: PysmtAccessSubset | None,
    ) -> Edge:
        """Adds a generic edge to the *current* graph."""
        return self.current_graph.add_edge(src, dst, subset)

    def add_reads_and_writes(
        self,
        node: Node,
        reads: list[tuple[Data, PysmtAccessSubset | None]],
        writes: list[tuple[Data, PysmtAccessSubset | None]],
    ):
        """
        Adds dataflow edges for a given node based on its read and write sets.
        A subset can be None to indicate that it should be inferred.

        This helper function encapsulates the common logic for creating incident edges
        for Compute and Structure nodes. It creates:
        1. Incoming edges from Data nodes for all accesses in `reads`.
        2. Outgoing edges from the `node` to Data nodes for all accesses in `writes`.
        It also asserts that any write has a corresponding read dependency on the same array.
        """
        for wd, wsubset in writes:
            # P3G Rule: Every write must be 'covered' by a read to establish a data dependency.
            # This implies a read-before-write semantic for hierarchical nodes.
            # To satisfy this, the (Data, subset) tuple representing the *output* of the write
            # (i.e., the second Data node returned by add_write_data, along with its subset)
            # must be present in the 'reads' list.
            if not any(
                (rd.array_id == wd.array_id and wsubset == rsubset)
                for rd, rsubset in reads
            ):
                assert False, (
                    f"Write to data region {wd.name}[{wsubset}] (array_id={wd.array_id}) "
                    f"is not covered by a corresponding read in the node's 'reads' list. "
                    f"P3G requires that all written data regions must also be considered 'read' "
                    f"to establish a dependency on their prior value. "
                    f"Ensure that for every write (Data_out, Subset), the tuple (Data_out, Subset) "
                    f"is also included in the 'reads' list. "
                    f"Reads provided: {reads}"
                )
        for data_node, subset in reads:
            self.add_edge(data_node, node, subset)

        for data_node, subset in writes:
            self.add_edge(node, data_node, subset)

    def add_compute(
        self,
        name: str,
        reads: list[tuple[Data, PysmtAccessSubset | None]],
        writes: list[tuple[Data, PysmtAccessSubset | None]],
    ) -> Compute:
        """
        Adds a Compute node and its access edges to the *current* graph.

        Args:
            name: The name of the compute node.
            reads: A list of (Data node, subset) tuples representing data read by the node.
            writes: A list of (Data node, subset) tuples representing data written by the node.

        Returns:
            A Compute node.
        """
        current_owner_node = self._get_current_owner_node()
        compute_node = Compute(
            name, graph=self.current_graph, parent=current_owner_node
        )
        self.current_graph.add_node(compute_node)
        self.add_reads_and_writes(compute_node, reads, writes)

        return compute_node

    def add_loop(
        self,
        name: str,
        loop_var_name: str,
        start: PysmtFormula,
        end: PysmtFormula,
        reads: list[tuple[Data, PysmtAccessSubset | None]],
        writes: list[tuple[Data, PysmtAccessSubset | None]],
    ) -> Loop:
        """
        Adds a sequential Loop and its dataflow edges to the *current* graph.
        """
        current_owner_node = self._get_current_owner_node()
        loop_node = Loop(
            name,
            self,
            loop_var_name,
            start,
            end,
            graph=self.current_graph,
            parent=current_owner_node,
        )
        self.current_graph.add_node(loop_node)
        self.add_reads_and_writes(loop_node, reads, writes)

        return loop_node

    def add_map(
        self,
        name: str,
        loop_var_name: str,
        start: PysmtFormula,
        end: PysmtFormula,
        reads: list[tuple[Data, PysmtAccessSubset | None]],
        writes: list[tuple[Data, PysmtAccessSubset | None]],
    ) -> Map:
        """Adds a parallel Map to the *current* graph."""
        current_owner_node = self._get_current_owner_node()
        map_node = Map(
            name,
            self,
            loop_var_name,
            start,
            end,
            graph=self.current_graph,
            parent=current_owner_node,
        )
        self.current_graph.add_node(map_node)
        self.add_reads_and_writes(map_node, reads, writes)

        return map_node

    def add_branch(
        self,
        name: str,
        reads: list[tuple[Data, PysmtAccessSubset | None]],
        writes: list[tuple[Data, PysmtAccessSubset | None]],
    ) -> Branch:
        """Adds a Branch to the *current* graph."""
        current_owner_node = self._get_current_owner_node()
        branch_node = Branch(
            name, self, graph=self.current_graph, parent=current_owner_node
        )
        self.current_graph.add_node(branch_node)
        self.add_reads_and_writes(branch_node, reads, writes)

        return branch_node

    def add_reduce(
        self,
        name: str,
        loop_var_name: str,
        start: PysmtFormula,
        end: PysmtFormula,
        wcr: PysmtFormula,
        reads: list[tuple[Data, PysmtAccessSubset | None]],
        writes: list[tuple[Data, PysmtAccessSubset | None]],
    ) -> Reduce:
        """Adds a parallel Reduce to the *current* graph."""
        current_owner_node = self._get_current_owner_node()
        reduce_node = Reduce(
            name,
            self,
            loop_var_name,
            start,
            end,
            wcr,
            graph=self.current_graph,
            parent=current_owner_node,
        )
        self.current_graph.add_node(reduce_node)
        self.add_reads_and_writes(reduce_node, reads, writes)

        return reduce_node

    def finish(self) -> Graph:
        """
        Finalizes the graph construction by propagating output and transient array information
        throughout the graph hierarchy. This method should be called after all nodes and
        edges have been added to the builder.
        """

        def _propagate_array_properties(graph: Graph):
            # Set outputs and transients for the current graph
            # This is a shallow copy, but since _is_output_arrays and _is_transient_arrays
            # are sets, they are mutable. If the intent is for each graph to have
            # its own independent set that could be modified later, a deep copy is needed.
            # For now, a direct assignment means all graphs share the same sets.
            graph.outputs = self._is_output_arrays
            graph.transients = self._is_transient_arrays

            # Recursively propagate to nested graphs
            for node in graph.nodes:
                if isinstance(node, (Map, Loop, Reduce)):
                    _propagate_array_properties(node.nested_graph)
                elif isinstance(node, Branch):
                    for _, nested_branch_graph in node.branches:
                        _propagate_array_properties(nested_branch_graph)

        _propagate_array_properties(self.root_graph)
        return self.root_graph


def _extract_reads_from_formula(
    formula: PysmtFormula, builder: "GraphBuilder"
) -> ReadSet:
    """
    Recursively extracts read accesses (array_id, subset) from a PysmtFormula,
    specifically looking for Select operations.
    """
    reads: ReadSet = []

    if formula.is_select():
        array_sym = formula.arg(0)
        index_expr = formula.arg(1)

        # Use the mapping from GraphBuilder to get the array_id
        if array_sym in builder._pysmt_array_sym_to_array_id:
            array_id = builder._pysmt_array_sym_to_array_id[array_sym]
            reads.append((array_id, index_expr))

    # Recursively check arguments
    for arg in formula.args():
        reads.extend(_extract_reads_from_formula(arg, builder))

    return reads


# ===================================================================
# --- SMT PATH MODEL BUILDER ---
# ===================================================================


def create_path_model_fn(loop_node: Loop) -> Callable[[PysmtSymbol], PathModel]:
    """
    Creates the 'path_model_fn' required by the SMT analyzer
    by analyzing the P3G structure inside the given loop.

    This returned function is what the SMT solver will call with
    its own iteration variables (e.g., 'i', 'j', 'k').
    """

    def _traverse(graph: Graph, current_predicate: PysmtFormula) -> PathModel:
        """
        Recursively walks the graph, collecting all paths and their
        predicates, ReadSets, and WriteSets.
        """
        all_paths: PathModel = []

        for node in graph.nodes:
            # Collect accesses from Compute nodes
            if isinstance(node, (Compute, Loop, Map, Reduce)):  # Only for Compute nodes
                W_set_node = node.get_write_set()
                R_set_node = node.get_read_set()
                if W_set_node or R_set_node:
                    all_paths.append((current_predicate, W_set_node, R_set_node))

            # Recursively traverse nested graphs
            elif isinstance(node, Branch):
                # Add the ReadSet from the branch's predicates
                P_R_set_branch = node.get_predicate_read_set()
                if P_R_set_branch:
                    # Predicate reads are unconditional for the branch decision
                    all_paths.append((current_predicate, [], P_R_set_branch))

                # Handle the ReadSet and WriteSet of the Branch node itself (from add_branch call)
                W_set_branch = node.get_write_set()
                R_set_branch = node.get_read_set()
                if W_set_branch or R_set_branch:
                    # These accesses are conditional on *any* path within the branch being taken.
                    # So, we need to form a disjunction of all internal branch predicates.
                    branch_internal_predicates = [pred for (pred, _) in node.branches]
                    if branch_internal_predicates:
                        # The predicate for these summary accesses is current_predicate AND (P1 OR P2 OR ...)
                        summary_predicate = _custom_simplify_formula(
                            And(current_predicate, Or(branch_internal_predicates))
                        )
                        all_paths.append(
                            (summary_predicate, W_set_branch, R_set_branch)
                        )
                    else:
                        # If there are no internal paths, these accesses are effectively unconditional
                        # (or the branch is empty, which is unusual).
                        # In this case, current_predicate is correct.
                        all_paths.append(
                            (current_predicate, W_set_branch, R_set_branch)
                        )

                for predicate, nested_graph in node.branches:
                    new_predicate = _custom_simplify_formula(
                        And(current_predicate, predicate)
                    )
                    branch_paths = _traverse(nested_graph, new_predicate)
                    all_paths.extend(branch_paths)

        return all_paths

    def recursive_substitute(subset_expr, substitution_map):
        """
        Recursively applies substitution to all components of a multi-dimensional index tuple.

        Args:
            subset_expr: The subset expression (PysmtFormula, PysmtRange, or PysmtCoordSet)
                         to apply substitution to.
            substitution_map: A dictionary mapping PysmtSymbols to their substitution values.

        Returns:
            The subset expression with substitutions applied.
        """
        """Recursively applies substitution to all components of a multi-dimensional index tuple."""
        if isinstance(subset_expr, PysmtRange):
            # Reconstruct PysmtRange explicitly
            return PysmtRange(
                recursive_substitute(subset_expr.start, substitution_map),
                recursive_substitute(subset_expr.end, substitution_map),
            )
        elif isinstance(subset_expr, PysmtCoordSet):
            # Reconstruct PysmtCoordSet explicitly
            return PysmtCoordSet(
                *(recursive_substitute(item, substitution_map) for item in subset_expr)
            )
        elif isinstance(subset_expr, PysmtSetMembershipPredicate):
            # Apply substitution to the wrapped formula and return a new predicate
            substituted_formula = substitute(subset_expr.formula, substitution_map)
            return PysmtSetMembershipPredicate(
                substituted_formula, subset_expr.member_symbol
            )
        else:
            # Base case: The item is a PysmtFormula; perform the substitution
            return substitute(subset_expr, substitution_map)

    internal_loop_var = loop_node.loop_var
    pre_calculated_paths = _traverse(loop_node.nested_graph, TRUE())

    def path_model_fn(solver_k: PysmtSymbol) -> PathModel:
        """
        This function is called by the SMT analyzer.
        It substitutes the solver's variable (solver_k) into the
        pre-calculated paths.
        """
        substitution_map = {internal_loop_var: solver_k}
        final_paths = []
        for predicate, W_set, R_set in pre_calculated_paths:
            subst_pred = recursive_substitute(predicate, substitution_map)

            # Use the recursive helper function for multi-dimensional index substitution
            subst_W_set = [
                (arr_id, recursive_substitute(subset, substitution_map))
                for (arr_id, subset) in W_set
            ]
            subst_R_set = [
                (arr_id, recursive_substitute(subset, substitution_map))
                for (arr_id, subset) in R_set
            ]
            final_paths.append((subst_pred, subst_W_set, subst_R_set))

        return final_paths

    return path_model_fn
