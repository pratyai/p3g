import os
import pathlib
import sys

import dace
from dace.properties import CodeBlock
from dace.sdfg import SDFG, InterstateEdge
from dace.sdfg.state import ConditionalBlock, ControlFlowRegion

# Add the project root to the sys.path
script_dir = os.path.dirname(__file__)
project_root = os.path.abspath(os.path.join(script_dir, os.pardir))
sys.path.insert(0, project_root)

# Define symbols
N = dace.symbol("N", dace.int32)
M = dace.symbol("M", dace.int32)


def generate_simple_loop_sdfg(name: str = "simple_loop") -> SDFG:
    """
    Generates an SDFG with a simple sequential loop:
    for i in range(N):
        A[i] = A[i-1] + B[i]
    """
    sdfg = SDFG(name)
    sdfg.add_array("A", [N], dace.float32)
    sdfg.add_array("B", [N], dace.float32)
    sdfg.add_symbol("i", dace.int32)  # Declare loop variable as symbol

    init_state = sdfg.add_state("init_state", is_start_block=True)

    # Define LoopRegion
    loop_region = dace.sdfg.state.LoopRegion(
        label="main_loop",
        condition_expr=f"i < {N}",
        loop_var="i",
        initialize_expr="i = 0",
        update_expr="i = i + 1",
        inverted=False,  # Standard for-loop
    )
    sdfg.add_node(loop_region)

    # Add states/nodes to the *inside* of the LoopRegion
    loop_state_inner = loop_region.add_state(
        "loop_state_inner", is_start_block=True
    )  # State *inside* the LoopRegion

    read_a_node = loop_state_inner.add_read("A")
    read_b_node = loop_state_inner.add_read("B")
    write_a_node = loop_state_inner.add_write("A")

    tasklet = loop_state_inner.add_tasklet(
        "compute",
        {"__a_in", "__b_in"},
        {"__a_out"},
        f"__a_out = __a_in + __b_in",
    )

    loop_state_inner.add_memlet_path(
        read_a_node,
        tasklet,
        memlet=dace.Memlet.simple(read_a_node.data, f"i-1"),
        dst_conn="__a_in",
    )
    loop_state_inner.add_memlet_path(
        read_b_node,
        tasklet,
        memlet=dace.Memlet.simple(read_b_node.data, f"i"),
        dst_conn="__b_in",
    )
    loop_state_inner.add_memlet_path(
        tasklet,
        write_a_node,
        memlet=dace.Memlet.simple(write_a_node.data, f"i"),
        src_conn="__a_out",
    )

    final_state = sdfg.add_state("final_state")

    # Connect init_state -> LoopRegion -> final_state
    sdfg.add_edge(init_state, loop_region, InterstateEdge())
    sdfg.add_edge(loop_region, final_state, InterstateEdge())

    return sdfg


def generate_conditional_sdfg(name: str = "conditional_loop") -> SDFG:
    """
    Generates an SDFG with a loop containing an if-else statement:
    for i in range(N):
        if A[i] > B[i]:
            C[i] = A[i] - B[i]
        else:
            C[i] = A[i] + B[i]
    """
    sdfg = SDFG(name)
    sdfg.add_array("A", [N], dace.float32)
    sdfg.add_array("B", [N], dace.float32)
    sdfg.add_array("C", [N], dace.float32)
    sdfg.add_symbol("i", dace.int32)  # Declare loop variable as symbol

    init_state = sdfg.add_state("init_state", is_start_block=True)

    # Define LoopRegion
    loop_region = dace.sdfg.state.LoopRegion(
        label="conditional_main_loop",
        condition_expr=f"i < {N}",
        loop_var="i",
        initialize_expr="i = 0",
        update_expr="i = i + 1",
        inverted=False,  # Standard for-loop
    )
    sdfg.add_node(loop_region)

    # Implement conditional logic using a ConditionalBlock
    conditional_block = ConditionalBlock()  # Instantiate the ConditionalBlock
    loop_region.add_node(conditional_block)  # Add it to the loop region

    # Create ControlFlowRegions for the if and else bodies
    if_cfr = ControlFlowRegion(f"if_body_{name}", sdfg=sdfg)
    else_cfr = ControlFlowRegion(f"else_body_{name}", sdfg=sdfg)

    # Add branches to the ConditionalBlock
    conditional_block.add_branch(CodeBlock(f"A[i] > B[i]"), if_cfr)
    conditional_block.add_branch(CodeBlock(f"A[i] <= B[i]"), else_cfr)

    # Add states and tasklets to the IF ControlFlowRegion
    if_state = if_cfr.add_state("if_state", is_start_block=True)
    read_a_if = if_state.add_read("A")
    read_b_if = if_state.add_read("B")
    write_c_if = if_state.add_write("C")
    tasklet_if = if_state.add_tasklet(
        "sub_comp", {"__a", "__b"}, {"__c"}, "__c = __a - __b"
    )
    if_state.add_memlet_path(
        read_a_if,
        tasklet_if,
        memlet=dace.Memlet.simple(read_a_if.data, "i"),
        dst_conn="__a",
    )
    if_state.add_memlet_path(
        read_b_if,
        tasklet_if,
        memlet=dace.Memlet.simple(read_b_if.data, "i"),
        dst_conn="__b",
    )
    if_state.add_memlet_path(
        tasklet_if,
        write_c_if,
        memlet=dace.Memlet.simple(write_c_if.data, "i"),
        src_conn="__c",
    )

    # Add states and tasklets to the ELSE ControlFlowRegion
    else_state = else_cfr.add_state("else_state", is_start_block=True)
    read_a_else = else_state.add_read("A")
    read_b_else = else_state.add_read("B")
    write_c_else = else_state.add_write("C")
    tasklet_else = else_state.add_tasklet(
        "add_comp", {"__a", "__b"}, {"__c"}, "__c = __a + __b"
    )
    else_state.add_memlet_path(
        read_a_else,
        tasklet_else,
        memlet=dace.Memlet.simple(read_a_else.data, "i"),
        dst_conn="__a",
    )
    else_state.add_memlet_path(
        read_b_else,
        tasklet_else,
        memlet=dace.Memlet.simple(read_b_else.data, "i"),
        dst_conn="__b",
    )
    else_state.add_memlet_path(
        tasklet_else,
        write_c_else,
        memlet=dace.Memlet.simple(write_c_else.data, "i"),
        src_conn="__c",
    )

    final_state = sdfg.add_state("final_state")

    # Connect init_state -> LoopRegion -> final_state
    sdfg.add_edge(init_state, loop_region, InterstateEdge())
    sdfg.add_edge(loop_region, final_state, InterstateEdge())

    return sdfg


def generate_nested_sdfg_example(name: str = "nested_sdfg") -> SDFG:
    """
    Generates an SDFG containing a nested SDFG.
    Outer: For i in range(N): A[i] = nested(B[i], C[i])
    Nested: res = in1 + in2
    """
    # Define the nested SDFG
    nested_sdfg = SDFG("nested_add")
    nested_sdfg.add_array("in1", [1], dace.float32)  # Removed transient=True
    nested_sdfg.add_array("in2", [1], dace.float32)  # Removed transient=True
    nested_sdfg.add_array("res", [1], dace.float32)  # Removed transient=True

    nested_state = nested_sdfg.add_state("nested_state", is_start_block=True)
    read_in1 = nested_state.add_read("in1")
    read_in2 = nested_state.add_read("in2")
    write_res = nested_state.add_write("res")
    tasklet = nested_state.add_tasklet(
        "add_task", {"_in1", "_in2"}, {"_res"}, "_res = _in1 + _in2"
    )

    nested_state.add_memlet_path(
        read_in1,
        tasklet,
        memlet=dace.Memlet.simple(read_in1.data, "0"),
        dst_conn="_in1",
    )
    nested_state.add_memlet_path(
        read_in2,
        tasklet,
        memlet=dace.Memlet.simple(read_in2.data, "0"),
        dst_conn="_in2",
    )
    nested_state.add_memlet_path(
        tasklet,
        write_res,
        memlet=dace.Memlet.simple(write_res.data, "0"),
        src_conn="_res",
    )

    # Define the outer SDFG
    sdfg = SDFG(name)
    sdfg.add_array("A", [N], dace.float32)
    sdfg.add_array("B", [N], dace.float32)
    sdfg.add_array("C", [N], dace.float32)
    sdfg.add_symbol("i", dace.int32)  # Declare loop variable as symbol

    init_state = sdfg.add_state("init_state", is_start_block=True)

    # Define LoopRegion for the outer loop
    outer_loop_region = dace.sdfg.state.LoopRegion(
        label="nested_sdfg_outer_loop",
        condition_expr=f"i < {N}",
        loop_var="i",
        initialize_expr="i = 0",
        update_expr="i = i + 1",
        inverted=False,
    )
    sdfg.add_node(outer_loop_region)

    # State *inside* the outer_loop_region where the nested_node resides
    loop_body_inner_state = outer_loop_region.add_state(
        "loop_body_inner_state", is_start_block=True
    )

    # Add access nodes to the outer_loop_region's internal state
    read_b_inner = loop_body_inner_state.add_read("B")
    read_c_inner = loop_body_inner_state.add_read("C")
    write_a_inner = loop_body_inner_state.add_write("A")

    # Add the nested SDFG node inside this state
    nested_node = loop_body_inner_state.add_nested_sdfg(
        nested_sdfg, inputs={"in1", "in2"}, outputs={"res"}, symbol_mapping={}
    )

    # Connect outer SDFG arrays to nested SDFG connectors via memlets
    loop_body_inner_state.add_memlet_path(
        read_b_inner,
        nested_node,
        memlet=dace.Memlet.simple(read_b_inner.data, f"i"),
        dst_conn="in1",
    )
    loop_body_inner_state.add_memlet_path(
        read_c_inner,
        nested_node,
        memlet=dace.Memlet.simple(read_c_inner.data, f"i"),
        dst_conn="in2",
    )
    loop_body_inner_state.add_memlet_path(
        nested_node,
        write_a_inner,
        memlet=dace.Memlet.simple(write_a_inner.data, f"i"),
        src_conn="res",
    )

    final_state = sdfg.add_state("final_state")

    # Connect init_state -> outer_loop_region -> final_state
    sdfg.add_edge(init_state, outer_loop_region, InterstateEdge())
    sdfg.add_edge(outer_loop_region, final_state, InterstateEdge())

    return sdfg


def generate_traditional_nested_loop_sdfg(
    name: str = "nested_loop_traditional",
) -> SDFG:
    """
    Generates an SDFG with a traditional nested loop:
    for i in range(N):
        for j in range(M):
            A[i,j] = A[i-1, j] + B[i,j]
    """
    sdfg = SDFG(name)
    sdfg.add_array("A", [N, M], dace.float32)  # 2D array
    sdfg.add_array("B", [N, M], dace.float32)  # 2D array
    sdfg.add_symbol("i", dace.int32)
    sdfg.add_symbol("j", dace.int32)

    init_state = sdfg.add_state("init_state", is_start_block=True)

    # Outer LoopRegion
    outer_loop_region = dace.sdfg.state.LoopRegion(
        label="outer_loop",
        condition_expr=f"i < {N}",
        loop_var="i",
        initialize_expr="i = 0",
        update_expr="i = i + 1",
        inverted=False,
    )
    sdfg.add_node(outer_loop_region)

    # Inner LoopRegion (added directly to the outer LoopRegion)
    inner_loop_region = dace.sdfg.state.LoopRegion(
        label="inner_loop",
        condition_expr=f"j < {M}",
        loop_var="j",
        initialize_expr="j = 0",
        update_expr="j = j + 1",
        inverted=False,
    )
    outer_loop_region.add_node(
        inner_loop_region, is_start_block=True
    )  # Add inner loop directly to outer loop

    # State inside the inner LoopRegion
    inner_loop_body_state = inner_loop_region.add_state(
        "inner_loop_body_state", is_start_block=True
    )

    read_a = inner_loop_body_state.add_read("A")
    read_b = inner_loop_body_state.add_read("B")
    write_a = inner_loop_body_state.add_write("A")

    tasklet = inner_loop_body_state.add_tasklet(
        "compute",
        {"__a_in", "__b_in"},
        {"__a_out"},
        f"__a_out = __a_in + __b_in",
    )

    # Memlets for the inner tasklet
    inner_loop_body_state.add_memlet_path(
        read_a,
        tasklet,
        memlet=dace.Memlet.simple(read_a.data, f"i-1, j"),  # A[i-1, j]
        dst_conn="__a_in",
    )
    inner_loop_body_state.add_memlet_path(
        read_b,
        tasklet,
        memlet=dace.Memlet.simple(read_b.data, f"i, j"),  # B[i, j]
        dst_conn="__b_in",
    )
    inner_loop_body_state.add_memlet_path(
        tasklet,
        write_a,
        memlet=dace.Memlet.simple(write_a.data, f"i, j"),  # A[i, j]
        src_conn="__a_out",
    )

    final_state = sdfg.add_state("final_state")

    # Connect init_state -> outer_loop_region -> final_state
    sdfg.add_edge(init_state, outer_loop_region, InterstateEdge())
    sdfg.add_edge(outer_loop_region, final_state, InterstateEdge())

    return sdfg


def main():
    output_dir = pathlib.Path(project_root) / "tools" / "demo"
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"Generating SDFG examples to {output_dir}")

    # Example 1: Simple Loop
    sdfg_simple_loop = generate_simple_loop_sdfg()
    sdfg_simple_loop.save(str(output_dir / "simple_loop.sdfgz"), compress=True)
    print(f"Generated simple_loop.sdfgz")
    sdfg_simple_loop.validate()

    # Example 2: Conditional Loop
    sdfg_conditional_loop = generate_conditional_sdfg()
    sdfg_conditional_loop.save(
        str(output_dir / "conditional_loop.sdfgz"), compress=True
    )
    print(f"Generated conditional_loop.sdfgz")
    sdfg_conditional_loop.validate()

    # Example 3: Nested SDFG (as a LoopRegion containing a NestedSDFG node)
    sdfg_nested = generate_nested_sdfg_example()
    sdfg_nested.save(str(output_dir / "nested_sdfg.sdfgz"), compress=True)
    print(f"Generated nested_sdfg.sdfgz")
    sdfg_nested.validate()

    # Example 4: Traditional Nested Loop (LoopRegion within a LoopRegion)
    sdfg_nested_traditional = generate_traditional_nested_loop_sdfg()
    sdfg_nested_traditional.save(
        str(output_dir / "nested_loop_traditional.sdfgz"), compress=True
    )
    print(f"Generated nested_loop_traditional.sdfgz")
    sdfg_nested_traditional.validate()

    print("All SDFG examples generated successfully.")


if __name__ == "__main__":
    main()
