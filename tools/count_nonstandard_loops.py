import dace
from dace.sdfg import nodes
from dace.sdfg.state import LoopRegion
import re


def analyze_sdfg_loops(path):
    print(f"Loading SDFG from {path}...")
    sdfg = dace.SDFG.from_file(path)

    non_standard_step_count = 0
    total_maps = 0
    total_loop_regions = 0

    print("Analyzing all nodes recursively for MapEntry nodes...")
    # This correctly finds MapEntry nodes everywhere
    for node, _ in sdfg.all_nodes_recursive():
        if isinstance(node, nodes.MapEntry):
            total_maps += 1
            for r in node.map.range:
                start, end, step = r
                try:
                    step_val = int(step)
                    if step_val != 1:
                        print(
                            f"  Found Map with non-standard step: {step_val} in Map '{node.map.label}'"
                        )
                        non_standard_step_count += 1
                except ValueError:
                    pass

    print("Analyzing all Control Flow Graphs for LoopRegion nodes...")

    # Use all_sdfgs_recursive() to get every SDFG object in the hierarchy
    # Then check the nodes (CFG nodes) of each SDFG
    all_sdfgs = list(sdfg.all_sdfgs_recursive())

    # Iterate over every SDFG object found
    for current_sdfg in all_sdfgs:
        # Check all nodes in this SDFG's CFG
        if hasattr(current_sdfg, "nodes"):  # Verify it has nodes (it should)
            for cfg_node in current_sdfg.nodes():
                if isinstance(cfg_node, LoopRegion):
                    total_loop_regions += 1
                    update_statement = cfg_node.update_statement

                    match = re.search(
                        r"=\s*([a-zA-Z_]\w*)\s*([+-])\s*(\S+)", str(update_statement)
                    )
                    if match:
                        step_val_str = match.group(3)
                        try:
                            step_value = int(step_val_str)
                            if step_value != 1:
                                print(
                                    f"  Found LoopRegion with non-standard step: {step_value} (Var: {cfg_node.loop_variable})"
                                )
                                non_standard_step_count += 1
                        except ValueError:
                            pass

                # Check if a region contains further nested regions (like LoopRegion inside LoopRegion)
                # LoopRegion IS an SDFG (subclass) in newer DaCe or contains a CFG.
                # If it's a ControlFlowRegion, it has .nodes(). We should traverse THOSE too.
                # all_sdfgs_recursive might not catch LoopRegions if they aren't implemented as NestedSDFG but just Regions.
                # So we need to recurse into Regions here if they are not SDFGs.

                if isinstance(
                    cfg_node, dace.sdfg.state.ControlFlowRegion
                ) and not isinstance(cfg_node, dace.SDFG):
                    # This is a Region (like LoopRegion, IfRegion) inside the SDFG.
                    # We need to scan ITS nodes too.
                    # A simple worklist for regions inside this SDFG is best.
                    pass  # Wait, let's just make a recursive function for regions.

    # Correct approach for Regions: Traverse the CFG hierarchy of the root SDFG
    # Because LoopRegions are nodes in the CFG, not NestedSDFGs.

    visited_regions = set()
    worklist = [sdfg]  # Start with root SDFG

    # Reset count to avoid double counting if I mix approaches
    total_loop_regions = 0
    non_standard_step_count_loops = 0

    while worklist:
        region = worklist.pop(0)
        if id(region) in visited_regions:
            continue
        visited_regions.add(id(region))

        # If it's a LoopRegion, count it
        if isinstance(region, LoopRegion):
            total_loop_regions += 1
            update_statement = region.update_statement
            match = re.search(
                r"=\s*([a-zA-Z_]\w*)\s*([+-])\s*(\S+)", str(update_statement)
            )
            if match:
                try:
                    step_value = int(match.group(3))
                    if step_value != 1:
                        print(
                            f"  Found LoopRegion with non-standard step: {step_value}"
                        )
                        non_standard_step_count_loops += 1
                except:
                    pass

        # Traverse children nodes (States or other Regions)
        if hasattr(region, "nodes"):
            for node in region.nodes():
                # If it's a region (LoopRegion, IfRegion, etc), add to worklist
                if isinstance(node, dace.sdfg.state.ControlFlowRegion):
                    worklist.append(node)
                # If it's a State, check for NestedSDFGs inside it
                elif isinstance(node, dace.SDFGState):
                    for data_node in node.nodes():
                        if isinstance(data_node, nodes.NestedSDFG):
                            worklist.append(data_node.sdfg)

    print("-" * 30)
    print(f"Total Maps: {total_maps}")
    print(f"Total LoopRegions: {total_loop_regions}")
    print(
        f"Total Non-Standard Step Loops found: {non_standard_step_count + non_standard_step_count_loops}"
    )


if __name__ == "__main__":
    analyze_sdfg_loops("tools/demo/cloudsc-sdfg/cloudsc.sdfgz")
