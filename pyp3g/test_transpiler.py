import textwrap
from .transpiler import PCodeTranspiler
from .types import assertion, sym, var, decl, out, Symbol, Array

# Global stubs for validity
N = Symbol("N")
M = Symbol("M")
i = Symbol("i")
A = Array("A")
B = Array("B")


class TestPCodeTranspiler:
    def _transpile(self, func, **kwargs):
        transpiler = PCodeTranspiler(**kwargs)
        return transpiler.transpile(func)

    def test_declarations_decorator_args(self):
        def code():
            pass

        pcode = self._transpile(
            code, syms=["N", "M"], vars=["i"], decls=["A", "B"], outs=["A"]
        )
        expected = textwrap.dedent("""
            sym N, M
            var i
            decl A, B
            out A
        """).strip()
        assert pcode.strip() == expected

    def test_assignment_op(self):
        def code():
            A[i] = B[i] + 1

        pcode = self._transpile(code)
        # AccessCollector should find B[i] and i (ignored) as reads, A[i] as write
        # P3G requires writes to be in reads: (A[i], B[i] => A[i])
        # Sorted order: A[i] comes before B[i]
        expected = "(A[i], B[i] => A[i]) | op(A[i] = B[i] + 1)"
        assert pcode.strip() == expected

    def test_aug_assignment_op(self):
        def code():
            A[i] += 1

        pcode = self._transpile(code)
        # A[i] read and written
        expected = "(A[i] => A[i]) | op(A[i] += 1)"
        assert pcode.strip() == expected

    def test_loop_idiomatic(self):
        def code():
            for i in range(1, N + 1):
                A[i] = A[i - 1]

        pcode = self._transpile(code)

        # Loops use zero indices. Writes (A[0]) added to reads.
        # Reads: A[0] (from A[i-1]), A[0] (from write A[i]). -> Unique A[0]
        expected = textwrap.dedent("""
            (A[0] => A[0]) L_i| for i = 1 to N:
                (A[i - 1], A[i] => A[i]) | op(A[i] = A[i - 1])
        """).strip()

        assert pcode.strip() == expected

    def test_branch_idiomatic(self):
        def code():
            if A[i] > 0:
                B[i] = A[i]

        pcode = self._transpile(code)

        # Branches use zero indices.
        # Reads: A[0] (condition), A[0] (body read). Writes: B[0].
        # P3G: Writes added to reads -> Reads: A[0], B[0].
        expected = textwrap.dedent("""
            (A[0], B[0] => B[0]) B| if A[i] > 0:
                (A[i], B[i] => B[i]) | op(B[i] = A[i])
        """).strip()
        assert pcode.strip() == expected

    def test_assertion(self):
        def code():
            assert N > 0

        pcode = self._transpile(code)
        expected = "! (> N 0)"
        assert pcode.strip() == expected
