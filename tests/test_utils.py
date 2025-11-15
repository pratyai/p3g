import io
import os
import sys
import multiprocessing
from multiprocessing import Process, Queue

from z3 import Z3Exception

from p3g.p3g import Graph, Compute, Branch, Loop, Map, Reduce, Data, WriteSet, ReadSet
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.shortcuts import Solver
from pysmt.smtlib.parser import SmtLibParser


# Custom Timeout Exception
class TimeoutError(Exception):
    pass


# --- Solver Configuration ---
SOLVER_NAME = "z3"  # Can be 'z3', 'cvc5', etc.
OUTPUT_DIR = "tmp/smt"


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


def print_p3g_structure(graph: Graph, indent=0):
    """Recursively prints the P3G structure."""

    # Print Graph Header/Name and Symbols
    s_indent = "  " * indent
    print(f"{s_indent}### {graph.name} ### (Symbols: {list(graph.symbols.keys())})")

    # 1. Print Data/Atomic Nodes (only at the root level for brevity)
    if indent == 0:
        data_nodes = [n for n in graph.nodes if isinstance(n, Data)]
        if data_nodes:
            print(
                f"{s_indent}  Data Nodes (IDs): {', '.join([f'{d.name} ({d.array_id}, Out: {d.is_output})' for d in data_nodes])}"
            )

    # 2. Print Control/Structure and Compute Nodes
    for node in graph.nodes:
        if isinstance(node, Compute):
            # Show Compute nodes as part of the dataflow
            writes = ", ".join(
                [
                    f"{e.dst.name}[{e.subset}]"
                    for e in node.out_edges
                    if isinstance(e.dst, Data)
                ]
            )
            reads = ", ".join(
                [
                    f"{e.src.name}[{e.subset}]"
                    for e in node.in_edges
                    if isinstance(e.src, Data)
                ]
            )
            print(f"{s_indent}  COMPUTE ({node.name}): Reads={reads}, Writes={writes}")

        elif isinstance(node, (Loop, Map, Reduce)):
            # Print accesses for the structure node itself (hierarchical edges)
            node_writes = ", ".join(
                [
                    f"{e.dst.name}[{e.subset}]"
                    for e in node.out_edges
                    if isinstance(e.dst, Data)
                ]
            )
            node_reads = ", ".join(
                [
                    f"{e.src.name}[{e.subset}]"
                    for e in node.in_edges
                    if isinstance(e.src, Data)
                ]
            )

            print(
                f"{s_indent}  {node.__class__.__name__} ({node.name}): iter={node.loop_var} in [{node.start}, {node.end}]"
            )
            if node_reads:
                print(f"{s_indent}    > Node Reads: {node_reads}")
            if node_writes:
                print(f"{s_indent}    > Node Writes: {node_writes}")

            print_p3g_structure(node.nested_graph, indent + 1)

        elif isinstance(node, Branch):
            # Print accesses for the Branch node itself
            node_writes = ", ".join(
                [
                    f"{e.dst.name}[{e.subset}]"
                    for e in node.out_edges
                    if isinstance(e.dst, Data)
                ]
            )
            node_reads = ", ".join(
                [
                    f"{e.src.name}[{e.subset}]"
                    for e in node.in_edges
                    if isinstance(e.src, Data)
                ]
            )
            predicate_reads = ", ".join(
                [
                    f"ID {arr_id}[{subset}]"
                    for arr_id, subset in node.get_predicate_read_set()
                ]
            )

            print(f"{s_indent}  BRANCH ({node.name})")
            if node_reads:
                print(f"{s_indent}    > Node Reads: {node_reads}")
            if node_writes:
                print(f"{s_indent}    > Node Writes: {node_writes}")
            if predicate_reads:
                print(f"{s_indent}    > Predicate Reads: {predicate_reads}")

            for pred, nested_graph in node.branches:
                print(f"{s_indent}    - IF: {pred}")
                print_p3g_structure(nested_graph, indent + 2)


# --- End of Graph Printing Utility ---


def _solve_smt_string_internal(smt_string: str, case_name: str, result_queue: Queue):
    """
    Internal function to solve the SMT query. Designed to be run in a separate process.
    Puts (result, model_str) or (exception,) into the queue.
    """
    filename = os.path.join(OUTPUT_DIR, f"{case_name}.smt2")

    # 1. Write the SMT string to the file (for inspection)
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    with open(filename, "w") as f:
        f.write(smt_string)

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
                    s.add_assertion(cmd.args[0])
                elif cmd.name == "declare-fun":
                    pass
                elif cmd.name == "check-sat":
                    break
                else:
                    pass

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
            result_queue.put((result, model_str))

    except SolverReturnedUnknownResultError as e:
        result_queue.put((e,))
    except Exception as e:
        result_queue.put((e,))


def solve_smt_string(
    smt_string: str, case_name: str, timeout_seconds: int = 30
) -> bool:
    """
    Saves the SMT query to a file and runs an in-memory pysmt solver
    (e.g., z3, cvc5) on the parsed string within a separate process with a timeout.
    Returns True for 'sat', False for 'unsat'.
    Raises TimeoutError if the solver exceeds the timeout.
    Raises other Exceptions for 'unknown' or solver failures.
    """
    print(f"SMT query saved to {os.path.join(OUTPUT_DIR, f'{case_name}.smt2')}")

    result_queue = Queue()
    process = Process(
        target=_solve_smt_string_internal, args=(smt_string, case_name, result_queue)
    )
    process.start()
    process.join(timeout=timeout_seconds)

    if process.is_alive():
        process.terminate()
        process.join()
        raise TimeoutError(
            f"SMT solver timed out after {timeout_seconds} seconds for case: {case_name}"
        )

    if not result_queue.empty():
        result_tuple = result_queue.get()
        if isinstance(result_tuple[0], Exception):
            # An exception occurred in the child process
            exc = result_tuple[0]
            if isinstance(exc, SolverReturnedUnknownResultError):
                raise exc
            else:
                print(f"Error: Solver '{SOLVER_NAME}' failed or is not installed.")
                print(f"Full error: {exc}")
                # Do not sys.exit(1) here, let pytest handle the failure
                raise exc
        else:
            # Normal SAT/UNSAT result
            result, model_str = result_tuple
            if result:
                print(f"Solver result: sat")
                print("--- Model ---")
                if model_str:
                    print(model_str)
                print(
                    "Note: The model only displays concrete values for symbols it could determine. "
                    "For arrays or other symbols without a concrete assignment, their values are not shown here. "
                    "You can query specific symbols by name if needed."
                )
                print("-------------")
                return True
            else:
                print(f"Solver result: unsat")
                return False
    else:
        # This case should ideally not be reached if the process finished without timeout
        # and put something in the queue.
        raise Exception("SMT solver process finished without returning a result.")
