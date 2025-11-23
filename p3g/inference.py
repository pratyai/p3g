import uuid
from collections import defaultdict

from pysmt.shortcuts import (
    substitute,
    Ite,
    LE,
    GE,
    get_free_variables,
    Symbol,
    And,
    Exists,
    Or,
)
from pysmt.typing import INT

from plum import dispatch  # Added plum import


from p3g.graph import Loop, Map, Reduce, Graph, Structure, Branch, Data
from p3g.subsets import (
    PysmtAccessSubset,
    PysmtSetMembershipPredicate,
    PysmtFormula,
    PysmtRange,
    _custom_simplify_formula,
    ReadSet,
    WriteSet,
    PysmtCoordSet,
    _get_set_membership_condition,
)


class InferenceEngine:
    """
    Infers read and write subsets for edges in the P3G that were left undefined (None)
    during graph construction.
    """

    def __init__(self, builder: "GraphBuilder"):
        self.builder = builder

    @dispatch
    def expand_subset(
        self, subset_to_expand: PysmtRange, current_structure_node: Loop | Map | Reduce
    ) -> PysmtRange:
        """
        Expands a PysmtRange in the context of the current outer loop.
        This dispatch is specific to Loop, Map, or Reduce nodes.
        """
        new_start = self._calculate_range_for_access(
            subset_to_expand.start, current_structure_node
        ).start
        new_end = _custom_simplify_formula(
            self._calculate_range_for_access(
                subset_to_expand.end, current_structure_node
            ).end
        )
        return PysmtRange(
            _custom_simplify_formula(new_start),
            _custom_simplify_formula(new_end),
        )

    @dispatch
    def expand_subset(
        self, subset_to_expand: PysmtCoordSet, current_structure_node: Structure
    ) -> PysmtCoordSet:
        """
        Expands a PysmtCoordSet by expanding its elements.
        """
        # Call self.expand_subset for recursive dispatch
        return PysmtCoordSet(
            *[
                self.expand_subset(elem, current_structure_node)
                for elem in subset_to_expand
            ]
        )

    @dispatch
    def expand_subset(
        self,
        subset_to_expand: PysmtSetMembershipPredicate,
        current_structure_node: Loop | Map | Reduce,
    ) -> PysmtSetMembershipPredicate:
        """
        Expands a PysmtSetMembershipPredicate. If its formula contains the loop variable
        of the current structure node, it performs existential quantification.
        """

        if current_structure_node.loop_var not in get_free_variables(
            subset_to_expand.formula
        ):
            return subset_to_expand

        # If the internal formula contains the loop variable of the current structure node,
        # we need to existentially quantify over that loop variable to capture its effect.
        loop_var_outer = current_structure_node.loop_var
        loop_start_outer = current_structure_node.start
        loop_end_outer = current_structure_node.end

        # Create a fresh bound variable for quantification to avoid capture issues
        k_bound_outer = Symbol(f"{loop_var_outer.symbol_name()}_outer_bound", INT)

        # Condition for the outer bound variable to be within its bounds
        loop_bounds_condition_outer = And(
            LE(loop_start_outer, k_bound_outer),
            LE(k_bound_outer, loop_end_outer),
        )

        # Substitute the outer bound variable into the inner formula
        substituted_inner_formula = substitute(
            subset_to_expand.formula, {loop_var_outer: k_bound_outer}
        )

        # Create the new formula with existential quantification
        new_formula = Exists(
            [k_bound_outer],
            And(loop_bounds_condition_outer, substituted_inner_formula),
        )
        return PysmtSetMembershipPredicate(
            new_formula,
            subset_to_expand.member_symbol,
            loop_start=current_structure_node.start,
            loop_end=current_structure_node.end,
        )

    @dispatch
    def expand_subset(
        self,
        subset_to_expand: PysmtFormula,
        current_structure_node: Loop | Map | Reduce,
    ) -> PysmtAccessSubset:
        """
        Expands a PysmtFormula into a PysmtSetMembershipPredicate if within a loop context.
        """
        # Create a fresh symbol for the member of the set
        fresh_member_sym = Symbol(f"v_set_{uuid.uuid4().hex[:8]}", INT)
        return _get_set_membership_condition(
            fresh_member_sym,
            subset_to_expand,
            current_structure_node.loop_var,
            current_structure_node.start,
            current_structure_node.end,
        ).to_concrete_access()

    @dispatch
    def expand_subset(
        self,
        subset_to_expand: PysmtAccessSubset | None,
        current_structure_node: Structure,
    ) -> PysmtAccessSubset | None:
        """Default case for None or unsupported types."""
        return subset_to_expand

    def _combine_subsets_for_array_id(
        self, unique_subsets: list[PysmtAccessSubset]
    ) -> PysmtAccessSubset:
        """
        Combines a list of unique subsets for a given array_id into a single
        PysmtAccessSubset. If multiple PysmtSetMembershipPredicate objects are present,
        their formulas are combined using Or (logical union). If there's a mix of
        types, they are combined into a PysmtCoordSet.

        Args:
            unique_subsets: A list of unique subsets (PysmtFormula, PysmtRange,
                            PysmtCoordSet, or PysmtSetMembershipPredicate) for a single array_id.

        Returns:
            A single PysmtAccessSubset representing the combined access for the array_id.
            This could be a PysmtSetMembershipPredicate, a PysmtCoordSet, or a single
            PysmtFormula/PysmtRange.
        """
        if not unique_subsets:
            # This case shouldn't happen if called correctly, but for safety.
            raise ValueError("unique_subsets cannot be empty.")

        if len(unique_subsets) == 1:
            return unique_subsets[0]

        # Separate predicates from other subsets
        predicate_subsets: list[PysmtSetMembershipPredicate] = []
        other_access_subsets: list[PysmtAccessSubset] = []
        for s in unique_subsets:
            if isinstance(s, PysmtSetMembershipPredicate):
                predicate_subsets.append(s)
            else:
                other_access_subsets.append(s)

        final_elements_for_coordset: list[PysmtAccessSubset] = []

        if predicate_subsets:
            # Combine all predicate formulas with Or
            # Assuming member_symbol is consistent across predicates for the same arr_id
            combined_predicate_formula = Or([s.formula for s in predicate_subsets])
            combined_predicate = PysmtSetMembershipPredicate(
                combined_predicate_formula, predicate_subsets[0].member_symbol
            )
            final_elements_for_coordset.append(combined_predicate)

        final_elements_for_coordset.extend(other_access_subsets)

        if len(final_elements_for_coordset) == 1:
            return final_elements_for_coordset[0]
        else:
            # If there's a mix or multiple results, wrap in PysmtCoordSet
            return PysmtCoordSet(*final_elements_for_coordset)

    def infer_all_accesses(self):
        """
        Traverses the entire P3G and infers subsets for all edges where the
        subset is None.
        """
        self._infer_graph_edges(self.builder.root_graph)

    def _calculate_range_for_access(
        self, formula: PysmtFormula, loop_node: Loop | Map | Reduce
    ) -> PysmtRange:
        """
        Calculates the effective PysmtRange for a given access formula
        within the context of a loop (Loop, Map, or Reduce node).
        Assumes the formula is monotonic with respect to the loop variable.
        The range is always returned in (min_value, max_value) order.
        """
        val_at_start_bound = _custom_simplify_formula(
            substitute(formula, {loop_node.loop_var: loop_node.start})
        )
        val_at_end_bound = _custom_simplify_formula(
            substitute(formula, {loop_node.loop_var: loop_node.end})
        )

        # Use Ite to symbolically determine the minimum and maximum of the two evaluated bounds.
        min_val = _custom_simplify_formula(
            Ite(
                LE(val_at_start_bound, val_at_end_bound),
                val_at_start_bound,
                val_at_end_bound,
            )
        )
        max_val = _custom_simplify_formula(
            Ite(
                GE(val_at_start_bound, val_at_end_bound),
                val_at_start_bound,
                val_at_end_bound,
            )
        )
        return PysmtRange(min_val, max_val)

    def _infer_graph_edges(self, graph: Graph):
        """
        Recursively traverses the graph, processing structural nodes first to infer
        subsets for their edges, and then recursing into their nested graphs.
        This ensures a bottom-up inference approach for nested structures.

        Args:
            graph: The Graph instance to infer edges for.
        """
        # We need to process nodes that define scopes (structures) first,
        # then recursively process their nested graphs.
        for node in graph.nodes:
            if isinstance(node, (Loop, Map, Reduce, Branch)):
                # First, recursively infer the children's edges to ensure bottom-up inference.
                if isinstance(node, (Loop, Map, Reduce)):
                    self._infer_graph_edges(node.nested_graph)
                elif isinstance(node, Branch):
                    for _, nested_graph in node.branches:
                        self._infer_graph_edges(nested_graph)

                # Now that the children's edges are inferred, infer the parent's edges.
                self._infer_edges_for_structure(node)

    def _infer_edges_for_structure(self, node: Structure):
        """
        Infers the subsets for the incoming and outgoing edges of a single
        structure node (e.g., Loop, Map, Reduce, Branch). It aggregates
        accesses from the node's nested graph(s) and uses them to determine
        the appropriate subsets for the structure's hierarchical edges.

        Args:
            node: The Structure node for which to infer edge subsets.
        """
        # This method is responsible for inferring the subsets for the incoming and
        # outgoing edges of a single structure node (e.g., a Loop).

        # Only proceed if there are edges with subsets that need inference.
        needs_inference = any(
            edge.subset is None for edge in node.in_edges + node.out_edges
        )
        if not needs_inference:
            return

        # 1. Aggregate all accesses from the nested graph(s).
        if isinstance(node, (Loop, Map, Reduce)):
            nested_reads, nested_writes = self._aggregate_nested_accesses(
                node.nested_graph, current_structure_node=node
            )
        elif isinstance(node, Branch):
            all_branch_reads: ReadSet = []
            all_branch_writes: WriteSet = []
            for _, nested_graph in node.branches:
                path_r, path_w = self._aggregate_nested_accesses(
                    nested_graph,
                    current_structure_node=node,  # Branch node itself is the parent
                )
                all_branch_reads.extend(path_r)
                all_branch_writes.extend(path_w)

            # Group accesses by array_id and then union their subsets
            merged_branch_reads: ReadSet = []
            grouped_reads = defaultdict(list)
            for arr_id, subset in all_branch_reads:
                grouped_reads[arr_id].append(subset)
            for arr_id, subsets in grouped_reads.items():
                # Filter out duplicate subsets for the same array_id
                unique_subsets = []
                for s in subsets:
                    if s not in unique_subsets:
                        unique_subsets.append(s)

                merged_branch_reads.append(
                    (arr_id, self._combine_subsets_for_array_id(unique_subsets))
                )

            merged_branch_writes: WriteSet = []
            grouped_writes = defaultdict(list)
            for arr_id, subset in all_branch_writes:
                grouped_writes[arr_id].append(subset)
            for arr_id, subsets in grouped_writes.items():
                # Filter out duplicate subsets for the same array_id
                unique_subsets = []
                for s in subsets:
                    if s not in unique_subsets:
                        unique_subsets.append(s)

                merged_branch_writes.append(
                    (arr_id, self._combine_subsets_for_array_id(unique_subsets))
                )

            nested_reads = merged_branch_reads
            nested_writes = merged_branch_writes

        else:
            return  # Should not happen

        # 2. Update incoming edges with inferred subsets.
        for edge in node.in_edges:
            if edge.subset is None:
                array_id = edge.src.array_id

                # Find all matching subsets from both reads and writes
                all_subsets = [
                    s for arr_id, s in nested_writes if arr_id == array_id
                ] + [s for arr_id, s in nested_reads if arr_id == array_id]

                # Filter for unique subsets
                unique_subsets = []
                for s in all_subsets:
                    if s not in unique_subsets:
                        unique_subsets.append(s)

                edge.subset = self._combine_subsets_for_array_id(unique_subsets)

        # 3. Update outgoing edges with inferred subsets.
        for edge in node.out_edges:
            if edge.subset is None:
                array_id = edge.dst.array_id

                # Find all matching subsets from writes
                all_subsets = [s for arr_id, s in nested_writes if arr_id == array_id]

                # Filter for unique subsets
                unique_subsets = []
                for s in all_subsets:
                    if s not in unique_subsets:
                        unique_subsets.append(s)

                edge.subset = self._combine_subsets_for_array_id(unique_subsets)

    def _aggregate_nested_accesses(
        self, graph: Graph, current_structure_node: Structure | None
    ) -> tuple[ReadSet, WriteSet]:
        """
        Aggregates all reads and writes from all nodes within a given graph.
        This is used for inferring accesses for parent structure nodes.
        """
        aggregated_reads: ReadSet = []
        aggregated_writes: WriteSet = []

        is_in_loop_context = isinstance(current_structure_node, (Loop, Map, Reduce))

        for node in graph.nodes:
            if isinstance(node, Data):
                continue

            # Process reads from the node's hierarchical edges
            for arr_id, subset in node.get_read_set():
                if is_in_loop_context:
                    aggregated_reads.append(
                        (arr_id, self.expand_subset(subset, current_structure_node))
                    )
                else:
                    aggregated_reads.append((arr_id, subset))

            # Process writes from the node's hierarchical edges
            for arr_id, subset in node.get_write_set():
                if is_in_loop_context:
                    aggregated_writes.append(
                        (arr_id, self.expand_subset(subset, current_structure_node))
                    )
                else:
                    aggregated_writes.append((arr_id, subset))

        return aggregated_reads, aggregated_writes
