import cocotb
from .. import helper
from .. import matrix

@cocotb.test()
async def test(dut):
    hs_dut = helper.HandshakeDut(dut)
    await hs_dut.init()
    
    for m, n, p in [
        (0, 0, 0),
        (2, 3, 2),
        (3, 2, 4),
        (4, 4, 4),
        (1, 5, 3),
        (5, 1, 2),
    ]:
        print(f"testing random matrix mul (m = {m}, n = {n}, p = {p})")
        a = matrix.random_matrix(m, n)
        b = matrix.random_matrix(n, p)
        await hs_dut.assert_io(
            [m, n, p], [None],
            init_memory={
                "a": sum(a, []),
                "b": sum(b, []),
            },
            expected_memory={
                "z": sum(matrix.matrix_mul(a, b), []),
            },
        )
