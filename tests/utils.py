import io
import time
import queue
from dataclasses import dataclass
from multiprocessing import Process, Queue
from typing import Optional

from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.shortcuts import Solver
from pysmt.smtlib.parser import SmtLibParser
from pysmt.walkers import IdentityDagWalker
from z3 import Z3Exception

from p3g.graph import Graph, Compute, Branch, Loop, Map, Reduce, Data, WriteSet, ReadSet


# Custom Timeout Exception
class TimeoutError(Exception):
    pass


@dataclass
class SmtResult:
    """Result of an SMT solver execution."""

    is_sat: bool
    time_elapsed: float
    model_str: Optional[str] = None
    num_quantifiers: int = 0
    num_atoms: int = 0
    num_and: int = 0
    num_or: int = 0
    formula_size: int = 0
    num_variables: int = 0
    num_arrays: int = 0


# --- Solver Configuration ---
SOLVER_NAME = "z3"  # Can be 'z3', 'cvc5', etc.


# --- Graph Printing Utility ---


def _aggregate_accesses(graph: Graph) -> tuple[WriteSet, ReadSet]:
    """
    Recursively collects all unique (array_id, subset) Write and Read access pairs
    from all Compute nodes within the graph and its nested structures.
    """
    aggregated_writes = []
    aggregated_reads = []

    for node in graph.nodes:
        if isinstance(node, Compute):
            # Base case: Collect accesses from Compute node
            aggregated_writes.extend(node.get_write_set())
            aggregated_reads.extend(node.get_read_set())

        elif isinstance(node, Branch):
            # Recursive case: Traverse branches
            for _, nested_graph in node.branches:
                w, r = _aggregate_accesses(nested_graph)
                aggregated_writes.extend(w)
                aggregated_reads.extend(r)

        elif isinstance(node, (Loop, Map, Reduce)):
            # Recursive case: Traverse nested loop/map body
            w, r = _aggregate_accesses(node.nested_graph)
            aggregated_writes.extend(w)
            aggregated_reads.extend(r)

    # Note: We return duplicates; distinctness relies on the consumer (human reader).
    return aggregated_writes, aggregated_reads


def get_p3g_structure_string(graph: Graph, indent=0) -> str:
    """Recursively returns a string representation of the P3G structure."""
    output_lines = []
    s_indent = "  " * indent

    # Sort symbols for consistent output
    sorted_symbols = sorted(list(graph.symbols.keys()))
    output_lines.append(f"{s_indent}### {graph.name} ### (Symbols: {sorted_symbols})")

    # 1. Print Data Nodes at the current level, sorted by name
    data_nodes = sorted(
        [n for n in graph.nodes if isinstance(n, Data)], key=lambda x: x.name
    )
    if data_nodes:
        output_lines.append(
            f"{s_indent}  Data Nodes (IDs): {', '.join([repr(d) for d in data_nodes])}"
        )

    # 2. Print Assertions
    if graph.assertions:
        output_lines.append(f"{s_indent}  Assertions:")
        for assertion in graph.assertions:
            output_lines.append(f"{s_indent}    - {assertion}")

    # 3. Print Control/Structure and Compute Nodes, sorted by name
    other_nodes = sorted(
        [n for n in graph.nodes if not isinstance(n, Data)], key=lambda x: x.name
    )

    for node in other_nodes:
        if isinstance(node, Compute):
            # Show Compute nodes as part of the dataflow
            writes = ", ".join(
                sorted(
                    [
                        f"{e.dst.name}[{e.subset}]"
                        for e in node.out_edges
                        if isinstance(e.dst, Data)
                    ]
                )
            )
            reads = ", ".join(
                sorted(
                    [
                        f"{e.src.name}[{e.subset}]"
                        for e in node.in_edges
                        if isinstance(e.src, Data)
                    ]
                )
            )
            output_lines.append(
                f"{s_indent}  {repr(node)}: Reads={reads}, Writes={writes}"
            )

        elif isinstance(node, (Loop, Map, Reduce)):
            # Print accesses for the structure node itself (hierarchical edges)
            node_writes = ", ".join(
                sorted(
                    [
                        f"{e.dst.name}[{e.subset}]"
                        for e in node.out_edges
                        if isinstance(e.dst, Data)
                    ]
                )
            )
            node_reads = ", ".join(
                sorted(
                    [
                        f"{e.src.name}[{e.subset}]"
                        for e in node.in_edges
                        if isinstance(e.src, Data)
                    ]
                )
            )

            output_lines.append(f"{s_indent}  {repr(node)}")
            if node_reads:
                output_lines.append(f"{s_indent}    > Node Reads: {node_reads}")
            if node_writes:
                output_lines.append(f"{s_indent}    > Node Writes: {node_writes}")

            output_lines.append(get_p3g_structure_string(node.nested_graph, indent + 1))

        elif isinstance(node, Branch):
            # Print accesses for the Branch node itself
            node_writes = ", ".join(
                sorted(
                    [
                        f"{e.dst.name}[{e.subset}]"
                        for e in node.out_edges
                        if isinstance(e.dst, Data)
                    ]
                )
            )
            node_reads = ", ".join(
                sorted(
                    [
                        f"{e.src.name}[{e.subset}]"
                        for e in node.in_edges
                        if isinstance(e.src, Data)
                    ]
                )
            )
            predicate_reads = ", ".join(
                sorted(
                    [
                        f"{graph._array_id_to_name[arr_id]}[{subset}]"
                        for arr_id, subset in node.get_predicate_read_set()
                    ]
                )
            )

            output_lines.append(f"{s_indent}  {repr(node)}")
            if node_reads:
                output_lines.append(f"{s_indent}    > Node Reads: {node_reads}")
            if node_writes:
                output_lines.append(f"{s_indent}    > Node Writes: {node_writes}")
            if predicate_reads:
                output_lines.append(
                    f"{s_indent}    > Predicate Reads: {predicate_reads}"
                )

            # Sort branches by predicate string for consistent output
            sorted_branches = sorted(node.branches, key=lambda x: str(x[0]))
            for pred, nested_graph in sorted_branches:
                output_lines.append(f"{s_indent}    - IF: {pred}")
                output_lines.append(get_p3g_structure_string(nested_graph, indent + 2))

    return "\n".join(output_lines)


def print_p3g_structure(graph: Graph, indent=0):
    """Recursively prints the P3G structure."""
    print(get_p3g_structure_string(graph, indent))


# --- End of Graph Printing Utility ---


class MetricsWalker(IdentityDagWalker):
    def __init__(self):
        super().__init__()
        self.num_quantifiers = 0
        self.num_atoms = 0
        self.num_and = 0
        self.num_or = 0
        self.formula_size = 0
        self.unique_variables = set()
        self.unique_arrays = set()

    def walk_forall(self, formula, args, **kwargs):
        self.num_quantifiers += 1
        self.formula_size += 1
        return formula

    def walk_exists(self, formula, args, **kwargs):
        self.num_quantifiers += 1
        self.formula_size += 1
        return formula

    def walk_and(self, formula, args, **kwargs):
        self.num_and += 1
        self.formula_size += 1
        return formula

    def walk_or(self, formula, args, **kwargs):
        self.num_or += 1
        self.formula_size += 1
        return formula

    def walk_symbol(self, formula, args, **kwargs):
        self.num_atoms += 1
        self.formula_size += 1
        if formula.symbol_type().is_array_type():
            self.unique_arrays.add(formula)
        else:
            self.unique_variables.add(formula)
        return formula

    def walk_int_constant(self, formula, args, **kwargs):
        self.formula_size += 1
        return formula

    def walk_real_constant(self, formula, args, **kwargs):
        self.formula_size += 1
        return formula

    def walk_bool_constant(self, formula, args, **kwargs):
        self.formula_size += 1
        return formula


def get_smt_metrics_from_string(smt_string: str) -> MetricsWalker:
    """
    Parses an SMT-LIB string, walks the formula to collect metrics,
    and returns them without invoking a solver.
    """
    parser = SmtLibParser()
    script = parser.get_script(io.StringIO(smt_string))

    walker = MetricsWalker()
    formula = None
    for cmd in script.commands:
        if cmd.name == "assert":
            formula = cmd.args[0]
            walker.walk(formula)
        elif cmd.name == "check-sat":
            break  # No formula to walk if check-sat is before assert or no assert

    if formula is None:
        raise ValueError(
            "No assert command found in SMT string to extract metrics from."
        )

    return walker


def _clean_with_z3(smt_string: str, tactic_names: list[str]):
    from z3 import Solver, Goal, Then, Tactic

    s = Solver()
    s.from_string(smt_string)
    assert s.assertions()
    g = Goal()
    g.add(s.assertions())

    tactics = [Tactic(name) for name in tactic_names]
    if len(tactics) == 1:
        (tactic,) = tactics
    else:
        tactic = Then(*tactics)

    result = tactic(g)
    output = Solver()
    for subgoal in result:
        for assertion in subgoal:
            output.add(assertion)
    return output.to_smt2()


def _solve_smt_string_internal(
    smt_string: str, result_queue: Queue, tactic_names: list[str]
):
    """
    Internal function to solve the SMT query. Designed to be run in a separate process.
    Puts (result, model_str) or (exception,) into the queue.
    """
    walker = get_smt_metrics_from_string(smt_string)
    smt_string = _clean_with_z3(smt_string, tactic_names=tactic_names)
    # 2. Parse the SMT-LIB string into pysmt formulas
    parser = SmtLibParser()
    script = parser.get_script(io.StringIO(smt_string))

    # 3. Run the solver using the pysmt API
    try:
        with Solver(name=SOLVER_NAME) as s:
            s.set_option(":quant_inst_max", 5000)
            s.set_option(
                ":timeout", 30000
            )  # Still set for internal solver, but multiprocessing handles hard timeout

            for cmd in script.commands:
                if cmd.name == "assert":
                    formula = cmd.args[0]
                    s.add_assertion(formula)
                elif cmd.name == "declare-fun":
                    pass
                elif cmd.name == "check-sat":
                    break
                else:
                    pass

            num_quantifiers = walker.num_quantifiers
            num_atoms = walker.num_atoms
            num_and = walker.num_and
            num_or = walker.num_or
            formula_size = walker.formula_size
            num_variables = len(walker.unique_variables)
            num_arrays = len(walker.unique_arrays)

            result: bool = s.check_sat()

            model_str = None
            if result:
                model = s.get_model()
                try:
                    model_str = str(model)
                except (NotImplementedError, Z3Exception) as e:
                    model_str = (
                        f"Cannot print model (sometime it's library's fault): {e}"
                    )
            result_queue.put(
                (
                    result,
                    model_str,
                    num_quantifiers,
                    num_atoms,
                    num_and,
                    num_or,
                    formula_size,
                    num_variables,
                    num_arrays,
                )
            )

    except SolverReturnedUnknownResultError as e:
        result_queue.put((e,))
    except Exception as e:
        result_queue.put((e,))


# --- Tactic Strategies ---
TACTIC_STRATEGIES = [
    ["qe"],
    ["simplify", "propagate-values"],
    ["simplify", "propagate-values", "ctx-solver-simplify", "qe-light"],
]


def solve_smt_string(smt_string: str, timeout_seconds: int = 30) -> SmtResult:
    """
    Runs multiple SMT solver strategies concurrently in separate processes.
    Returns the result from the first strategy that finishes with SAT or UNSAT.
    Cancels pending strategies once a result is obtained.
    """
    processes = []
    result_queue = Queue()

    # Start all strategy processes
    for tactic_names in TACTIC_STRATEGIES:
        p = Process(
            target=_solve_smt_string_internal,
            args=(smt_string, result_queue, tactic_names),
        )
        p.start()
        processes.append(p)

    start_time = time.time()
    final_result = None
    last_exception = None

    try:
        while True:
            # Check for overall timeout
            elapsed = time.time() - start_time
            if timeout_seconds and elapsed > timeout_seconds:
                raise TimeoutError(
                    f"All SMT strategies timed out after {timeout_seconds}s"
                )

            # Check if all processes are dead
            if not any(p.is_alive() for p in processes) and result_queue.empty():
                break

            try:
                # Poll queue with a short timeout to allow checking overall timeout
                # effectively busy-wait but with sleep
                result_tuple = result_queue.get(timeout=0.1)
            except queue.Empty:
                continue

            # Process result
            if isinstance(result_tuple[0], Exception):
                # Strategy failed with error (e.g. unknown result)
                # Just record it and keep waiting for others
                last_exception = result_tuple[0]
                continue

            # Success! (SAT or UNSAT)
            (
                result,
                model_str,
                num_quantifiers,
                num_atoms,
                num_and,
                num_or,
                formula_size,
                num_variables,
                num_arrays,
            ) = result_tuple

            # Construct SmtResult
            if result:
                print(f"Solver result: sat")
                if model_str:
                    print(f"--- Model ---\n{model_str}\n-------------")
                final_result = SmtResult(
                    is_sat=True,
                    time_elapsed=elapsed,  # Approximation
                    model_str=model_str,
                    num_quantifiers=num_quantifiers,
                    num_atoms=num_atoms,
                    num_and=num_and,
                    num_or=num_or,
                    formula_size=formula_size,
                    num_variables=num_variables,
                    num_arrays=num_arrays,
                )
            else:
                print(f"Solver result: unsat")
                final_result = SmtResult(
                    is_sat=False,
                    time_elapsed=elapsed,
                    num_quantifiers=num_quantifiers,
                    num_atoms=num_atoms,
                    num_and=num_and,
                    num_or=num_or,
                    formula_size=formula_size,
                    num_variables=num_variables,
                    num_arrays=num_arrays,
                )

            # We found a valid result, break loop
            break

    finally:
        # Cleanup: Terminate all processes
        for p in processes:
            if p.is_alive():
                p.terminate()
                p.join()

    if final_result:
        return final_result

    if last_exception:
        if isinstance(last_exception, SolverReturnedUnknownResultError):
            raise last_exception
        else:
            print(f"Error: Solver '{SOLVER_NAME}' failed.")
            print(f"Full error: {last_exception}")
            raise last_exception

    raise Exception(
        "SMT solver failed to produce a result with any tactic (all failed or timed out)."
    )
