import cocotb
from .. import helper
from .. import matrix

def nn_norm(src, N, max_val, shift):
    dest = [0] * N

    def nn_norm_aux(i):
        cond = i < N
        if cond:
            v = src[i]
            prod = v * max_val
            scaled = prod >> shift
            dest[i] = scaled

            one = 1
            j = i + one
            nn_norm_aux(j)
        else:
            return

    start = 0
    nn_norm_aux(start)
    return dest

@cocotb.test()
async def test(dut):
    hs_dut = helper.HandshakeDut(dut)
    await hs_dut.init()

    for N, max_val, shift in [
        (16, 255, 8),
        (25, 1023, 10),
    ]:
        print(f"testing nn_norm (N = {N}, max_val = {max_val}, shift = {shift})")
        src = matrix.random_matrix(1, N, lower=0, upper=255)
        await hs_dut.assert_io(
            [max_val, shift, N],
            [None],
            init_memory={
                "src": sum(src, []),
            },
            expected_memory={
                "dest": nn_norm(sum(src, []), N, max_val, shift),
            },
        )
