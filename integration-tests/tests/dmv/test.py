import cocotb
from .. import helper
from .. import matrix

@cocotb.test()
async def test(dut):
    hs_dut = helper.HandshakeDut(dut)
    await hs_dut.init()
    
    for m, n in [
        (0, 0),
        (0, 1),
        (2, 3),
        (3, 2),
        (4, 4),
        (1, 5),
        (5, 1),
    ]:
        print(f"testing random matrix-vector mul (m = {m}, n = {n})")
        a = matrix.random_matrix(m, n)
        b = matrix.random_matrix(n, 1)
        await hs_dut.assert_io(
            [m, n], [None],
            init_memory={
                "a": sum(a, []),
                "x": sum(b, []),
            },
            expected_memory={
                "y": sum(matrix.matrix_mul(a, b), []),
            },
        )
