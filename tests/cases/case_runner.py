from typing import Callable, List, Tuple, Any

from p3g.graph import Graph, Loop, PysmtFormula
from tests.utils import print_p3g_structure, solve_smt_string


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

    result = solve_smt_string(smt_query, test_name, timeout_seconds=timeout_seconds)

    if expected_result:
        assert result, f"Expected {test_name} to be SAT but SMT solver returned UNSAT."
    else:
        assert not result, (
            f"Expected {test_name} to be UNSAT but SMT solver returned SAT."
        )

    print(
        f"\nVerdict: PASSED. {test_name} is {'SAT' if expected_result else 'UNSAT'} as expected."
    )
