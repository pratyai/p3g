import itertools
from typing import List, Dict, Tuple, Callable, Set, Union, Optional

from pysmt.formula import FNode  # Correct import
from pysmt.shortcuts import (
    Symbol, INT, And, TRUE, substitute, simplify, Or
)

# --- Pysmt Type Aliases for Clarity ---
PysmtFormula = FNode
PysmtSymbol = FNode

# Type aliases
ReadSet = List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]
WriteSet = List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]
PathModel = List[Tuple[PysmtFormula, WriteSet, ReadSet]]

# Define __all__ for 'from p3g import *'
__all__ = [
    'Node', 'Edge', 'Graph', 'Data', 'Compute', 'Structure',
    'Map', 'Loop', 'Branch', 'Reduce', 'GraphBuilder',
    'PathContext',
    'PysmtFormula', 'PysmtSymbol',
    'create_path_model_fn',
    'PathModel', 'ReadSet', 'WriteSet'  # Export type aliases
]


# --- Base Graph Components ---

class Node:
    """
    Base class for all nodes in the P3G.
    Represents V_D, V_C, and V_S.
    """

    def __init__(self, name: str):
        self.name = name
        self.in_edges: List['Edge'] = []
        self.out_edges: List['Edge'] = []

    def __repr__(self):
        return f"{self.__class__.__name__}({self.name})"


class Edge:
    """
    Represents a dataflow edge (E) in the P3G.
    It carries a symbolic subset annotation (a pysmt formula or a range tuple).
    """

    def __init__(self, src: Node, dst: Node, subset: Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]):
        self.src = src
        self.dst = dst
        self.subset = subset

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
        self.nodes: List[Node] = []
        self.edges: List[Edge] = []
        self.symbols: Dict[str, PysmtSymbol] = {}
        self.outputs: Set[Data] = set()

    def add_node(self, node: Node):
        self.nodes.append(node)

    def add_edge(self, src: Node, dst: Node, subset: Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]) -> Edge:
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

    def __init__(self, name: str, array_id: int, is_output: bool = False):
        super().__init__(name)
        self.array_id = array_id
        self.is_output = is_output

    def __repr__(self):
        return f"Data({self.name}, id={self.array_id})"


class Compute(Node):
    """
    A computation node (V_C).
    Its data accesses are defined *by its incident edges*.
    """

    def __init__(self, name: str):
        super().__init__(name)

    def get_read_set(self) -> List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]:
        """
        Generates the ReadSet by inspecting incoming edges from Data nodes.
        """
        read_set = []
        for edge in self.in_edges:
            if isinstance(edge.src, Data):
                read_set.append((edge.src.array_id, edge.subset))
        return read_set

    def get_write_set(self) -> List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]:
        """
        Generates the WriteSet by inspecting outgoing edges to Data nodes.
        """
        write_set = []
        for edge in self.out_edges:
            if isinstance(edge.dst, Data):
                write_set.append((edge.dst.array_id, edge.subset))
        return write_set


# --- Structure Nodes (V_S) ---

class Structure(Node):
    """
    Base class for hierarchical structure nodes (V_S).
    """

    def __init__(self, name: str, builder: 'GraphBuilder'):
        super().__init__(name)
        self.builder = builder


class Map(Structure):
    """A parallel Map node."""

    def __init__(self, name: str, builder: 'GraphBuilder', loop_var_name: str, start: PysmtFormula, end: PysmtFormula):
        super().__init__(name, builder)
        self.loop_var = Symbol(loop_var_name, INT)
        self.start = start
        self.end = end
        self.nested_graph = Graph(f"{name}_body")

    def __enter__(self):
        self.builder.graph_stack.append(self.nested_graph)
        return self  # Return self so user can access loop_var

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.builder.graph_stack.pop()

    def get_read_set(self) -> List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]:
        """
        Generates the ReadSet by inspecting incoming edges from Data nodes.
        """
        read_set = []
        for edge in self.in_edges:
            if isinstance(edge.src, Data):
                read_set.append((edge.src.array_id, edge.subset))
        return read_set

    def get_write_set(self) -> List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]:
        """
        Generates the WriteSet by inspecting outgoing edges to Data nodes.
        """
        write_set = []
        for edge in self.out_edges:
            if isinstance(edge.dst, Data):
                write_set.append((edge.dst.array_id, edge.subset))
        return write_set


class Loop(Structure):
    """A sequential Loop node."""

    def __init__(self, name: str, builder: 'GraphBuilder', loop_var_name: str, start: PysmtFormula, end: PysmtFormula):
        super().__init__(name, builder)
        self.loop_var = Symbol(loop_var_name, INT)
        self.start = start
        self.end = end
        self.nested_graph = Graph(f"{name}_body")

    def __enter__(self):
        self.builder.graph_stack.append(self.nested_graph)
        return self  # Return self so user can access loop_var

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.builder.graph_stack.pop()

    def get_read_set(self) -> List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]:
        """
        Generates the ReadSet by inspecting incoming edges from Data nodes.
        """
        read_set = []
        for edge in self.in_edges:
            if isinstance(edge.src, Data):
                read_set.append((edge.src.array_id, edge.subset))
        return read_set

    def get_write_set(self) -> List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]:
        """
        Generates the WriteSet by inspecting outgoing edges to Data nodes.
        """
        write_set = []
        for edge in self.out_edges:
            if isinstance(edge.dst, Data):
                write_set.append((edge.dst.array_id, edge.subset))
        return write_set


class Branch(Structure):
    """
    A Branch node.
    Contains multiple arms, each with a predicate and a nested graph.
    """

    def __init__(self, name: str, builder: 'GraphBuilder'):
        super().__init__(name, builder)
        self.branches: List[Tuple[PysmtFormula, Graph]] = []

    def add_path(self, predicate: PysmtFormula) -> 'PathContext':
        """Adds a new conditional path and returns its context."""
        path_graph = Graph(f"{self.name}_branch_{len(self.branches)}")
        self.branches.append((predicate, path_graph))
        return PathContext(self.builder, path_graph)

    def __enter__(self):
        """Allows 'with b.add_branch(...) as branch:' syntax."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """No action needed on exit."""
        pass

    def get_read_set(self) -> List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]:
        """
        Generates the ReadSet by inspecting incoming edges from Data nodes.
        """
        read_set = []
        for edge in self.in_edges:
            if isinstance(edge.src, Data):
                read_set.append((edge.src.array_id, edge.subset))
        return read_set

    def get_write_set(self) -> List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]:
        """
        Generates the WriteSet by inspecting outgoing edges to Data nodes.
        """
        write_set = []
        for edge in self.out_edges:
            if isinstance(edge.dst, Data):
                write_set.append((edge.dst.array_id, edge.subset))
        return write_set

    def get_predicate_read_set(self) -> ReadSet:
        """
        Extracts the ReadSet from the predicates of this Branch node.
        """
        all_predicate_reads: ReadSet = []
        for (predicate, _) in self.branches:
            all_predicate_reads.extend(_extract_reads_from_formula(predicate, self.builder))
        return all_predicate_reads


class Reduce(Structure):
    """A parallel Reduce node."""

    def __init__(self, name: str, builder: 'GraphBuilder', loop_var_name: str, start: PysmtFormula, end: PysmtFormula,
                 wcr: PysmtFormula):
        super().__init__(name, builder)
        self.loop_var = Symbol(loop_var_name, INT)
        self.start = start
        self.end = end
        self.wcr = wcr
        self.nested_graph = Graph(f"{name}_body")

    def __enter__(self):
        self.builder.graph_stack.append(self.nested_graph)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.builder.graph_stack.pop()

    def get_read_set(self) -> List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]:
        """
        Generates the ReadSet by inspecting incoming edges from Data nodes.
        """
        read_set = []
        for edge in self.in_edges:
            if isinstance(edge.src, Data):
                read_set.append((edge.src.array_id, edge.subset))
        return read_set

    def get_write_set(self) -> List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]:
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

    def __init__(self, builder: 'GraphBuilder', graph: Graph):
        self.builder = builder
        self.graph = graph

    def __enter__(self):
        self.builder.graph_stack.append(self.graph)

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.builder.graph_stack.pop()


# --- The Builder Class ---

class GraphBuilder:
    """
    Uses a recursive builder pattern (with context managers)
    to construct a P3G.
    """

    def __init__(self):
        self.root_graph = Graph("root")
        self.graph_stack: List[Graph] = [self.root_graph]

        self._data_id_map: Dict[str, int] = {}
        self._next_data_id: int = 10001
        self._pysmt_array_sym_to_array_id: Dict[PysmtSymbol, int] = {}

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
        """Returns the graph context currently at the top of the stack."""
        return self.graph_stack[-1]

    def add_symbol(self, name: str, type=INT) -> PysmtSymbol:
        """Adds a symbol to the root graph."""
        return self.root_graph.add_symbol(name, type)

    def add_data(self, name: str, is_output: bool = False, pysmt_array_sym: Optional[PysmtSymbol] = None) -> Data:
        """
        Adds a Data node to the *current* graph. This node represents a
        local reference to a named data container.
        """
        # The array_id represents the underlying unique data container.
        array_id = self._get_data_id(name)

        # Create a new Data node instance for the current graph context.
        data_node = Data(name, array_id, is_output)

        # Add the new node to the current graph.
        self.current_graph.add_node(data_node)

        # If an associated PysmtSymbol for the array content is provided, map it to the array_id.
        if pysmt_array_sym:
            self._pysmt_array_sym_to_array_id[pysmt_array_sym] = array_id

        # The 'is_output' flag applies globally to the root graph.
        if is_output:
            self.root_graph.outputs.add(data_node)

        return data_node

    def add_edge(self, src: Node, dst: Node, subset: Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]) -> Edge:
        """Adds a generic edge to the *current* graph."""
        return self.current_graph.add_edge(src, dst, subset)

    def add_reads_and_writes(self, node: Node,
                             reads: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]],
                             writes: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]):
        """
        Adds dataflow edges for a given node based on its read and write sets.

        This helper function encapsulates the common logic for creating incident edges
        for Compute and Structure nodes. It creates:
        1. Incoming edges from Data nodes to the `node` for all data in `reads` and `writes`.
           (This implies that data that is written is also considered "read" for the purpose of
           establishing an incoming dependency edge, as per the P3G model's interpretation
           of hierarchical edges).
        2. Outgoing edges from the `node` to Data nodes for all data in `writes`.

        Args:
            node: The target Node (Compute or Structure) for which to add edges.
            reads: A list of (Data node, subset) tuples representing data read by the node.
            writes: A list of (Data node, subset) tuples representing data written by the node.
        """
        for data_node, subset in itertools.chain(reads, writes):
            self.add_edge(data_node, node, subset)

        for data_node, subset in writes:
            self.add_edge(node, data_node, subset)

    def add_compute(self, name: str,
                    reads: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]],
                    writes: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]) -> Compute:
        """
        Adds a Compute node and its access edges to the *current* graph.
        """
        compute_node = Compute(name)
        self.current_graph.add_node(compute_node)
        self.add_reads_and_writes(compute_node, reads, writes)

        return compute_node

    def add_loop(self, name: str, loop_var_name: str, start: PysmtFormula, end: PysmtFormula,
                 reads: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]],
                 writes: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]) -> Loop:
        """
        Adds a sequential Loop and its dataflow edges to the *current* graph.
        """
        loop_node = Loop(name, self, loop_var_name, start, end)
        self.current_graph.add_node(loop_node)
        self.add_reads_and_writes(loop_node, reads, writes)

        return loop_node

    def add_map(self, name: str, loop_var_name: str, start: PysmtFormula, end: PysmtFormula,
                reads: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]],
                writes: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]) -> Map:
        """Adds a parallel Map to the *current* graph."""
        map_node = Map(name, self, loop_var_name, start, end)
        self.current_graph.add_node(map_node)
        self.add_reads_and_writes(map_node, reads, writes)

        return map_node

    def add_branch(self, name: str,
                   reads: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]],
                   writes: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]) -> Branch:
        """Adds a Branch to the *current* graph."""
        branch_node = Branch(name, self)
        self.current_graph.add_node(branch_node)
        self.add_reads_and_writes(branch_node, reads, writes)

        return branch_node

    def add_reduce(self, name: str, loop_var_name: str, start: PysmtFormula, end: PysmtFormula,
                   wcr: PysmtFormula,
                   reads: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]],
                   writes: List[Tuple[Data, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]) -> Reduce:
        """Adds a parallel Reduce to the *current* graph."""
        reduce_node = Reduce(name, self, loop_var_name, start, end, wcr)
        self.current_graph.add_node(reduce_node)
        self.add_reads_and_writes(reduce_node, reads, writes)

        return reduce_node


def _extract_reads_from_formula(formula: PysmtFormula, builder: 'GraphBuilder') -> ReadSet:
    """
    Recursively extracts read accesses (array_id, subset) from a PysmtFormula,
    specifically looking for Select operations.
    """
    reads: ReadSet = []

    if formula.is_select():
        array_sym = formula.arg(0)  # This is the PysmtSymbol for the array (e.g., B_val)
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

# Type aliases
ReadSet = List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]
WriteSet = List[Tuple[int, Union[PysmtFormula, Tuple[PysmtFormula, PysmtFormula]]]]
PathModel = List[Tuple[PysmtFormula, WriteSet, ReadSet]]


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
            if isinstance(node, Compute):  # Only for Compute nodes
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
                        summary_predicate = simplify(And(current_predicate, Or(branch_internal_predicates)))
                        all_paths.append((summary_predicate, W_set_branch, R_set_branch))
                    else:
                        # If there are no internal paths, these accesses are effectively unconditional
                        # (or the branch is empty, which is unusual).
                        # In this case, current_predicate is correct.
                        all_paths.append((current_predicate, W_set_branch, R_set_branch))

                for (predicate, nested_graph) in node.branches:
                    new_predicate = simplify(And(current_predicate, predicate))
                    branch_paths = _traverse(nested_graph, new_predicate)
                    all_paths.extend(branch_paths)
            elif isinstance(node, (Loop, Map, Reduce)):
                nested_paths = _traverse(node.nested_graph, current_predicate)
                all_paths.extend(nested_paths)

        return all_paths

    def recursive_substitute(formula_or_tuple, substitution_map):
        """Recursively applies substitution to all components of a multi-dimensional index tuple."""
        # Check if it's a collection (tuple or list)
        if isinstance(formula_or_tuple, (tuple, list)):
            # Recursively apply substitution to each element
            return type(formula_or_tuple)(
                recursive_substitute(item, substitution_map)
                for item in formula_or_tuple
            )
        else:
            # Base case: The item is a PysmtFormula; perform the substitution
            return substitute(formula_or_tuple, substitution_map)

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
        for (predicate, W_set, R_set) in pre_calculated_paths:
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
