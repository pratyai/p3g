# --- Pysmt Type Aliases for Clarity ---
import uuid

import z3
from pysmt.fnode import FNode
from pysmt.shortcuts import (
    And,
    substitute,
    Equals,
    Exists,
    LE,
    Symbol,
    simplify,
    get_env,
    Or,
    FALSE,
    get_free_variables,
    TRUE,
)
from pysmt.solvers.z3 import Z3Converter
from pysmt.typing import INT

PysmtFormula = FNode
PysmtSymbol = FNode


class PysmtSetMembershipPredicate:
    """
    Represents a PysmtFormula that serves as a characteristic function
    (membership predicate) for a set of values.

    This class wraps a boolean PysmtFormula, providing a distinct runtime type
    to indicate its semantic meaning. It stores the underlying boolean formula
    and the symbolic variable for which membership is being checked.
    """

    def __init__(
        self,
        formula: PysmtFormula,
        member_symbol: PysmtSymbol,
        loop_start: PysmtFormula | None = None,
        loop_end: PysmtFormula | None = None,
    ):
        if not formula.is_bool_op():
            raise TypeError(
                "PysmtSetMembershipPredicate must wrap a boolean PysmtFormula."
            )
        self._formula: PysmtFormula = formula
        self._member_symbol: PysmtSymbol = member_symbol
        self._loop_start: PysmtFormula | None = loop_start
        self._loop_end: PysmtFormula | None = loop_end

    @property
    def formula(self) -> PysmtFormula:
        """The underlying boolean PysmtFormula representing the membership predicate."""
        return self._formula

    @property
    def member_symbol(self) -> PysmtSymbol:
        """The symbolic variable for which membership is being checked."""
        return self._member_symbol

    @property
    def loop_start(self) -> PysmtFormula | None:
        """The loop start bound associated with this predicate, if it originated from a loop."""
        return self._loop_start

    @property
    def loop_end(self) -> PysmtFormula | None:
        """The loop end bound associated with this predicate, if it originated from a loop."""
        return self._loop_end

    def to_concrete_access(
        self,
    ) -> PysmtFormula | PysmtRange | PysmtCoordSet | "PysmtSetMembershipPredicate":
        """
        Attempts to simplify the membership predicate into a more concrete access type
        (PysmtFormula for a point, PysmtRange for a 1D range, PysmtCoordSet for multi-dim,
        or itself if no further simplification is possible).
        """
        simplified_formula = _custom_simplify_formula(self.formula)

        # Case 1: Point access (member_symbol == expr)
        # We need to find if simplified_formula is of the form Equals(self.member_symbol, some_expression)
        if simplified_formula.is_equals():
            if (
                simplified_formula.arg(0) == self.member_symbol
                and not simplified_formula.arg(1).is_bool()
            ):
                return simplified_formula.arg(1)
            elif (
                simplified_formula.arg(1) == self.member_symbol
                and not simplified_formula.arg(0).is_bool()
            ):
                return simplified_formula.arg(0)

        # Case 2: Range access (Lower <= member_symbol <= Upper)
        if simplified_formula.is_and():
            conjuncts = simplified_formula.args()
            if len(conjuncts) == 2:
                # Check for LE(Lower, member_symbol) and LE(member_symbol, Upper)
                le1 = None
                le2 = None
                for c in conjuncts:
                    if c.is_le():
                        if c.arg(1) == self.member_symbol:  # Lower <= member_symbol
                            le1 = c
                        elif c.arg(0) == self.member_symbol:  # member_symbol <= Upper
                            le2 = c
                if le1 is not None and le2 is not None:
                    lower_bound = le1.arg(0)
                    upper_bound = le2.arg(1)
                    return PysmtRange(lower_bound, upper_bound)

        # Case 3: For Exists patterns, we cannot do much, return self.
        if simplified_formula.is_exists():
            return self

        # Default: Cannot simplify further, return self
        return self

    def __repr__(self):
        return f"PysmtSetMembershipPredicate(for={self._member_symbol}, predicate={self._formula})"


class PysmtRange(tuple[PysmtFormula, PysmtFormula]):
    """
    Represents a 1D range using two PysmtFormulas for start and end.
    Inherits from tuple to maintain tuple-like behavior.
    """

    def __new__(cls, start: PysmtFormula, end: PysmtFormula):
        # Ensure that the elements are PysmtFormula instances
        if not isinstance(start, PysmtFormula) or not isinstance(end, PysmtFormula):
            raise TypeError("PysmtRange elements must be PysmtFormula instances.")
        return super().__new__(cls, (start, end))

    @property
    def start(self) -> PysmtFormula:
        return self[0]

    @property
    def end(self) -> PysmtFormula:
        return self[1]

    def __repr__(self):
        return f"PysmtRange({self.start}, {self.end})"


class PysmtCoordSet(tuple[PysmtFormula | PysmtRange, ...]):
    """
    Represents a multi-dimensional coordinate or a set of ranges.
    It's a tuple of PysmtFormula and/or PysmtRange objects.
    """

    def __new__(
        cls, *elements: PysmtFormula | PysmtRange | PysmtSetMembershipPredicate
    ):
        for element in elements:
            if not isinstance(
                element,
                (PysmtFormula, PysmtRange, PysmtCoordSet, PysmtSetMembershipPredicate),
            ):
                raise TypeError(
                    "PysmtCoordSet elements must be PysmtFormula or PysmtRange instances."
                )
        return super().__new__(cls, elements)

    def __repr__(self):
        return f"PysmtCoordSet{super().__repr__()}"


# Type aliases
PysmtAccessSubset = (
    PysmtFormula | PysmtRange | PysmtCoordSet | PysmtSetMembershipPredicate
)
ReadSet = list[tuple[int, PysmtAccessSubset]]
WriteSet = list[tuple[int, PysmtAccessSubset]]


def _custom_simplify_with_z3(formula: PysmtFormula) -> PysmtFormula:
    """
    Simplifies a PysmtFormula using Z3, ensuring an explicit Z3 context
    is used for conversion, simplification, and solver operations.
    This helps in canonicalizing expressions for more reliable comparisons.

    Args:
        formula: The PysmtFormula to be simplified.

    Returns:
        The simplified PysmtFormula.
    """
    local_env = get_env()
    # local_env = Environment()
    # 1. Initialize an explicit Z3 Context
    ctx = z3.Context()
    # 2. Pass the explicit context to the converter
    to_z3 = Z3Converter(local_env, ctx)
    z3_expr = to_z3.convert(formula)
    # 3. Simplify the expression (it uses the context of its operands)
    z3_simplified = z3.simplify(z3_expr)
    # Check sort to determine if wrapping is necessary
    if z3_simplified.sort().kind() == z3.Z3_BOOL_SORT:
        z3_assertion = z3_simplified
    else:
        # Use the Python equality operator (==) on Z3 expressions
        # to create the (E == E) assertion *within the context* of the operands
        z3_assertion = z3_simplified == z3_simplified
    # 4. Initialize the solver using the same explicit context
    solver = z3.SolverFor("ALL", ctx=ctx)
    # This assertion should now succeed as z3_assertion and solver share the same context
    solver.add(z3_assertion)
    # Convert to SMT-LIB string
    smtlib_string = solver.to_smt2()
    # Parse the SMT-LIB script back into a pySMT FNode
    parser = SmtLibParser(local_env)
    script = parser.get_script(StringIO(smtlib_string))
    pysmt_result_assertion = script.get_last_formula()
    # Unwrap the term if it was a non-Boolean term wrapped in Eq(E, E)
    if z3_simplified.sort().kind() != z3.Z3_BOOL_SORT:
        return pysmt_result_assertion.args()[0]
    else:
        return pysmt_result_assertion


def _custom_simplify_formula(formula: PysmtFormula) -> PysmtFormula:
    """
    Simplifies a PysmtFormula using the default PySMT simplifier.
    This function serves as a wrapper to `pysmt.shortcuts.simplify`.

    Args:
        formula: The PysmtFormula to be simplified.

    Returns:
        The simplified PysmtFormula.
    """
    return simplify(formula)


def _get_set_membership_condition(
    member_sym: PysmtSymbol,
    access_formula: PysmtFormula,
    loop_var: PysmtSymbol,
    loop_start: PysmtFormula,
    loop_end: PysmtFormula,
) -> PysmtSetMembershipPredicate:
    """
    Constructs a PysmtFormula (an existential quantification) that describes
    the condition for `member_sym` to be an element of the set of values
    that `access_formula` takes as `loop_var` iterates from `loop_start` to `loop_end`.

    This function defines the set's elements precisely, handling potential
    non-monotonicity and "holes" in the set of values.

    Symbolically, it returns the formula:
    `Exists k_bound . (loop_start <= k_bound <= loop_end) AND (member_sym == substitute(access_formula, {loop_var: k_bound}))`

    Args:
        member_sym: A PysmtSymbol representing an arbitrary potential member of the set (e.g., 'v').
        access_formula: The PysmtFormula representing the access expression (e.g., `i`, `N-1-i`).
        loop_var: The PysmtSymbol representing the loop variable (k).
        loop_start: The PysmtFormula representing the inclusive start bound (S).
        loop_end: The PysmtFormula representing the inclusive end bound (T).

    Returns:
        A PysmtFormula (a boolean expression) representing the existential condition
        for `member_sym` to be in the set.
    """
    # Create a fresh bound variable for quantification to avoid capture issues
    k_bound = Symbol(f"{loop_var.symbol_name()}_bound", INT)

    # Condition for the bound variable to be within its bounds
    loop_bounds_condition = And(LE(loop_start, k_bound), LE(k_bound, loop_end))

    # Substitute the bound variable into the access_formula
    substituted_access_formula = substitute(access_formula, {loop_var: k_bound})

    # Condition that 'member_sym' is equal to the substituted access_formula
    member_equals_formula_condition = Equals(member_sym, substituted_access_formula)

    # Existentially quantify 'k_bound'
    return PysmtSetMembershipPredicate(
        Exists([k_bound], And(loop_bounds_condition, member_equals_formula_condition)),
        member_sym,
        loop_start=loop_start,
        loop_end=loop_end,
    )


def _create_range_intersection_formula(
    range1: PysmtRange, range2: PysmtRange
) -> PysmtFormula:
    """
    Generates a pysmt formula asserting that two 1D ranges intersect.
    A range is represented as a tuple (start, end).
    Intersection condition: (start1 <= end2) AND (start2 <= end1)
    """
    start1, end1 = range1
    start2, end2 = range2
    return And(LE(start1, end2), LE(start2, end1))


def _to_membership_predicate_for_intersection(
    access_subset: PysmtAccessSubset, member_sym: PysmtSymbol
) -> PysmtSetMembershipPredicate:
    """
    Converts any PysmtAccessSubset into a PysmtSetMembershipPredicate using the provided member_sym.
    This helper makes intersection logic more uniform by operating on a single type.
    """
    if isinstance(access_subset, PysmtSetMembershipPredicate):
        # If it's already a predicate, and its member_symbol is different from the target member_sym,
        # we need to substitute. If they are the same, no substitution is needed.
        if access_subset.member_symbol == member_sym:
            return access_subset
        else:
            # Create a new predicate where the formula is re-expressed in terms of the new member_sym
            return PysmtSetMembershipPredicate(
                substitute(
                    access_subset.formula, {access_subset.member_symbol: member_sym}
                ),
                member_sym,
            )
    elif isinstance(access_subset, PysmtRange):
        # A range (start, end) corresponds to the predicate (start <= member_sym <= end)
        return PysmtSetMembershipPredicate(
            And(LE(access_subset.start, member_sym), LE(member_sym, access_subset.end)),
            member_sym,
        )
    elif isinstance(access_subset, PysmtFormula):
        # A point access 'X' corresponds to the predicate (member_sym == X)
        return PysmtSetMembershipPredicate(
            Equals(member_sym, access_subset), member_sym
        )
    elif isinstance(access_subset, PysmtCoordSet):
        # A PysmtCoordSet represents a tuple of indices/ranges.
        # If we are converting it to a 1D PysmtSetMembershipPredicate, it implies
        # that the CoordSet itself must represent a single point or range.
        # If it contains multiple elements, we'll need to define what it means
        # to intersect a multi-dimensional set with a 1D predicate.
        # For now, let's assume a 1D context for this intersection logic,
        # so CoordSet will only be convertible if it has a single element.
        if len(access_subset) == 1:
            return _to_membership_predicate_for_intersection(
                access_subset[0], member_sym
            )
        else:
            # Intersection of multi-dimensional CoordSet with 1D PysmtSetMembershipPredicate
            # is complex and currently unsupported. Return a false predicate.
            return PysmtSetMembershipPredicate(FALSE(), member_sym)
    else:
        return PysmtSetMembershipPredicate(FALSE(), member_sym)  # Safety catch


def _create_intersection_formula(
    idx1: PysmtAccessSubset,
    idx2: PysmtAccessSubset,
) -> PysmtFormula:
    """
    Creates a pysmt formula asserting that two indices or ranges intersect.
    This function handles single indices (points), 1D ranges, and multi-dimensional
    coordinate sets, and PysmtSetMembershipPredicate. Intersection is checked dimension by dimension,
    or semantically for predicates.

    - Point vs. Point: Intersection is equality.
    - Range vs. Range: Intersection is classic range overlap.
    - Point vs. Range: Intersection is checking if the point is within the range.
    - CoordSet vs. CoordSet: Intersection is the conjunction of intersections
      of their corresponding elements.
    - PysmtSetMembershipPredicate vs. Any: Converts both to predicates and uses existential quantification.

    Args:
        idx1: The first index, range, or coordinate set.
        idx2: The second index, range, or coordinate set.

    Returns:
        A PysmtFormula that is TRUE if the two inputs intersect, and FALSE otherwise.
        Returns FALSE if dimensions of CoordSets do not match.
    """

    # Prioritize CoordSet vs. CoordSet intersection if both are CoordSets
    if isinstance(idx1, PysmtCoordSet) and isinstance(idx2, PysmtCoordSet):
        if len(idx1) != len(idx2):
            return FALSE()  # Different dimensions cannot intersect
        intersections = [
            _create_intersection_formula(i1, i2) for i1, i2 in zip(idx1, idx2)
        ]
        return And(intersections) if intersections else TRUE()

    # Handle PysmtSetMembershipPredicate for any remaining cases
    elif isinstance(idx1, PysmtSetMembershipPredicate) or isinstance(
        idx2, PysmtSetMembershipPredicate
    ):
        # If at least one is a PysmtSetMembershipPredicate, convert both to predicates
        # and quantify existentially over a fresh symbol.
        fresh_v_symbol = Symbol(f"v_intersect_{uuid.uuid4().hex[:8]}", INT)

        smp_idx1 = _to_membership_predicate_for_intersection(idx1, fresh_v_symbol)
        smp_idx2 = _to_membership_predicate_for_intersection(idx2, fresh_v_symbol)

        result_formula = Exists(
            [fresh_v_symbol], And(smp_idx1.formula, smp_idx2.formula)
        )
        print(f"DEBUG: Predicate intersection result: {result_formula}")
        return result_formula

    elif isinstance(idx1, PysmtRange) and isinstance(idx2, PysmtRange):
        return _create_range_intersection_formula(idx1, idx2)

    elif isinstance(idx1, PysmtFormula) and isinstance(idx2, PysmtFormula):
        return Equals(idx1, idx2)

    elif isinstance(idx1, PysmtRange) and isinstance(idx2, PysmtFormula):
        start, end = idx1
        return And(LE(start, idx2), LE(idx2, end))

    elif isinstance(idx1, PysmtFormula) and isinstance(idx2, PysmtRange):
        start, end = idx2
        return And(LE(start, idx1), LE(idx1, end))

    else:
        # This case handles mixed types that are not PysmtSetMembershipPredicate and not explicitly handled above.
        raise TypeError(
            f"Unsupported intersection types: {type(idx1)} and {type(idx2)}"
        )


def _create_set_intersection_formula(
    set_a: ReadSet, set_b: WriteSet, id_to_symbol_map: dict[int, PysmtSymbol]
) -> PysmtFormula:
    """
    Creates a pysmt formula representing the intersection of two access sets.

    This function generates a disjunction of clauses, where each clause represents
    a potential intersection between an access in `set_a` and an access in `set_b`.
    An intersection occurs if two accesses are to the same array (`array_id`)
    and their indices/ranges intersect.

    Args:
        set_a: The first set of accesses (e.g., a ReadSet).
        set_b: The second set of accesses (e.g., a WriteSet).
        id_to_symbol_map: A dictionary mapping array_id to its corresponding PysmtSymbol.

    Returns:
        A PysmtFormula that is TRUE if any access in `set_a` intersects with any
        access in `set_b`. Returns FALSE if there are no intersections or if either
        set is empty.
    """
    clauses = []
    if not set_a or not set_b:
        return FALSE()

    for arr_a, idx_a in set_a:
        for arr_b, idx_b in set_b:
            # Only check for intersection if the accesses are to the same array
            if arr_a == arr_b:
                arr_a_node = id_to_symbol_map[arr_a]
                arr_b_node = id_to_symbol_map[arr_b]
                index_intersection = _create_intersection_formula(idx_a, idx_b)
                clauses.append(And(Equals(arr_a_node, arr_b_node), index_intersection))

    if not clauses:
        return FALSE()
    elif len(clauses) == 1:
        return clauses[0]
    else:
        return Or(clauses)


# Helper for recursive free variable extraction (needed for multi-dimensional access tuples)
def _get_free_variables_recursive(
    formula_or_tuple: PysmtAccessSubset,
) -> set[PysmtSymbol]:
    """Recursively extracts free variables from a formula or a tuple/list of formulas."""

    if isinstance(formula_or_tuple, PysmtSetMembershipPredicate):
        # Recursively get free variables from its formula and member_symbol
        free_vars = set(get_free_variables(formula_or_tuple.formula))
        free_vars.update(get_free_variables(formula_or_tuple.member_symbol))
        return free_vars
    elif isinstance(formula_or_tuple, (PysmtRange, PysmtCoordSet)):
        # Recursive case: Traverse all elements in the multi-dimensional index tuple/list
        free_vars = set()
        for item in formula_or_tuple:
            free_vars.update(_get_free_variables_recursive(item))
        return free_vars
    else:
        # Base case: The item is a PysmtFormula
        return get_free_variables(formula_or_tuple)
