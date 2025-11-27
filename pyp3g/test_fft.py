import pytest

from p3g.parser import PseudocodeParser
from .decorator import pcode
from .types import Array, Symbol

# Global symbols and arrays for FFT tests
N = Symbol("N")  # FFT size
X = Array("X")  # Input array
Y = Array("Y")  # Output array


@pcode(
    syms=[
        "N",
        "rev_i",
        "block_size",
        "half_block_size",
        "idx_even",
        "idx_odd",
        "temp_even",
        "temp_odd",
    ],
    vars=["i", "s", "k"],
    decls=["X", "Y"],
    outs=["Y"],
)
def cooley_tukey_algo():
    assert N > 0
    # Cooley-Tukey FFT (simplified, illustrative)
    # This implementation will focus on capturing the control flow and array
    # accesses characteristic of a CT FFT, rather than full mathematical correctness.
    # N is assumed to be a power of 2.

    # Let's consider a simple bit-reversal permutation and then logN stages
    # of butterfly operations.

    # Bit-reversal permutation (simplified)
    # In real FFT, this depends on N. For transpilation, we illustrate accesses.
    for i in range(0, N):
        rev_i = Symbol("rev_i")  # Placeholder for bit-reversed i
        # This would typically be a bit manipulation, here it's an assignment
        # that the transpiler should handle.
        X[rev_i] = X[i]  # Illustrative access

    # logN stages
    for s in range(0, N):  # s for stage (illustrative, not logN stages)
        block_size = Symbol("block_size")  # 2^s
        half_block_size = Symbol("half_block_size")  # 2^(s-1)
        for k in range(0, N, block_size):
            for i in range(0, half_block_size):
                idx_even = k + i
                idx_odd = k + i + half_block_size

                temp_even = Y[idx_even]  # Read
                temp_odd = Y[idx_odd]  # Read

                Y[idx_even] = temp_even + temp_odd  # Write
                Y[idx_odd] = temp_even - temp_odd  # Write


@pcode(
    syms=["N", "idx1", "idx2", "val1", "val2", "s_idx1", "s_idx2", "s_val1", "s_val2"],
    vars=["p", "q", "p_prime", "q_prime"],
    decls=["X", "Y"],
    outs=["Y"],
)
def stockham_algo():
    assert N > 0
    # Stockham FFT (simplified, illustrative)
    # This implementation will also focus on capturing the control flow and array
    # accesses characteristic of a Stockham FFT.

    # A typical Stockham involves multiple passes over the data,
    # using ping-pong buffers or strided accesses.
    # Here, we illustrate two passes.

    # Pass 1
    for p in range(0, N):
        for q in range(0, N // 2):  # N/2 groups
            # Illustrative strided access
            idx1 = p * 2 + q
            idx2 = p * 2 + q + N

            val1 = X[idx1]  # Read
            val2 = X[idx2]  # Read

            Y[idx1] = val1 + val2  # Write
            Y[idx2] = val1 - val2  # Write

    # Pass 2 (Illustrative, could be more complex striding or permuting)
    # This pass might operate on Y and write back to X or another buffer.
    # For simplicity, let's assume it operates on Y and writes to Y with different strides.
    for p_prime in range(0, N // 2):  # N/2 elements per "row"
        for q_prime in range(0, N):
            # More complex striding (illustrative)
            s_idx1 = p_prime + q_prime * (N // 2)
            s_idx2 = p_prime + (q_prime + N // 2) * (N // 2)

            s_val1 = Y[s_idx1]  # Read
            s_val2 = Y[s_idx2]  # Read

            Y[s_idx1] = s_val1 * s_val2  # Write (Illustrative operation)
            Y[s_idx2] = s_val1 / s_val2  # Write (Illustrative operation)


class TestFFTTranspilation:
    def _transpile_and_parse(self, func):
        pcode_str = func.pcode()

        parser = PseudocodeParser()
        try:
            graph = parser.parse(pcode_str)
            # Add print to check for exceptions if needed
            print(f"\n--- Transpilation successful for {func.__name__} ---")
            return graph, pcode_str
        except Exception as e:
            print(
                f"\n--- P3G Parser failed for {func.__name__}: {e} ---"
            )  # Add print here
            pytest.fail(
                f"P3G Parser failed to parse generated pcode for {func.__name__}: {e}\nGenerated PCode:\n{pcode_str}"
            )

    def test_cooley_tukey_fft(self):
        graph, pcode_str = self._transpile_and_parse(cooley_tukey_algo)
        print(f"\n--- Cooley-Tukey PCode ---\n{pcode_str}\n--------------------------")

        # Basic verification: ensure some loops and ops are present
        assert "L_i| for i = 0 to (N - 1):" in pcode_str
        assert "op(X[rev_i] = X[i])" in pcode_str
        assert "L_s| for s = 0 to (N - 1):" in pcode_str
        assert "L_k| for k = 0 to (N - 1):" in pcode_str
        assert "L_i| for i = 0 to (half_block_size - 1):" in pcode_str
        assert "op(Y[idx_even] = temp_even + temp_odd)" in pcode_str
        assert "op(Y[idx_odd] = temp_even - temp_odd)" in pcode_str

    def test_stockham_fft(self):
        graph, pcode_str = self._transpile_and_parse(stockham_algo)
        print(f"\n--- Stockham PCode ---\n{pcode_str}\n------------------------")

        # Basic verification: ensure some loops and ops are present

        assert "L_p| for p = 0 to (N - 1):" in pcode_str
        assert "L_q| for q = 0 to ((N // 2) - 1):" in pcode_str
        assert "op(Y[idx1] = (val1 + val2))" in pcode_str
        assert "op(Y[idx2] = (val1 - val2))" in pcode_str
        assert "L_p_prime| for p_prime = 0 to ((N // 2) - 1):" in pcode_str
        assert "L_q_prime| for q_prime = 0 to (N - 1):" in pcode_str
        assert "op(Y[s_idx1] = (s_val1 * s_val2))" in pcode_str
        assert "op(Y[s_idx2] = (s_val1 / s_val2))" in pcode_str
