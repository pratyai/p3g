import os
from typing import Callable, List, Tuple, Any

from p3g.graph import Graph, Loop, PysmtFormula
from tests.utils import print_p3g_structure, solve_smt_string

OUTPUT_DIR = "tmp/smt"


def run_test_case(
    graph_builder: Callable[[], Tuple[Graph, Loop, Any]],
    smt_generator: Callable[[Loop, List[PysmtFormula], bool], str],
    test_name: str,
    expected_result: bool,
    extra_assertions: List[PysmtFormula] = None,
    extra_info: str = "",
    loop_node_index: int = 1,
    timeout_seconds: int = None,
):
    """
    A helper function to run a single test case.
    """
    print(
        f"\n--- Running Test: {test_name} (Expected: {'SAT' if expected_result else 'UNSAT'}) {extra_info} ---"
    )

    # The graph builder can return a variable number of arguments
    graph_components = graph_builder()
    b_root_graph = graph_components[0]
    loop_node = graph_components[loop_node_index]

    print_p3g_structure(b_root_graph)

    print(f"Generating SMT query for {test_name}.")
    smt_query = smt_generator(loop_node, extra_assertions, False)
    print(f"\n--- Generated SMT Query ({test_name}) ---")
    print(smt_query)
    print("--------------------------------------------------")

    if test_name:
        # Write the SMT string to the file (for inspection)
        print(f"SMT query saved to {os.path.join(OUTPUT_DIR, f'{test_name}.smt2')}")
        filename = os.path.join(OUTPUT_DIR, f"{test_name}.smt2")
        os.makedirs(OUTPUT_DIR, exist_ok=True)
        with open(filename, "w") as f:
            f.write(smt_query)

    smt_result = solve_smt_string(smt_query, timeout_seconds=timeout_seconds)
    result = smt_result.is_sat
    elapsed = smt_result.time_elapsed

    if expected_result:
        assert result, f"Expected {test_name} to be SAT but SMT solver returned UNSAT."
    else:
        assert not result, (
            f"Expected {test_name} to be UNSAT but SMT solver returned SAT."
        )

    print(
        f"\nVerdict: PASSED. {test_name} is {'SAT' if expected_result else 'UNSAT'} as expected. (Time: {elapsed:.4f}s, "
        f"Quantifiers: {smt_result.num_quantifiers}, Atoms: {smt_result.num_atoms}, "
        f"And: {smt_result.num_and}, Or: {smt_result.num_or}, Size: {smt_result.formula_size})"
    )
