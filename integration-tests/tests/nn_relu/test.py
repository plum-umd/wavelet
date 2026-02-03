import cocotb
from .. import helper
from .. import matrix

def nn_relu(src, N):
    dest = [0] * N
    
    def sel(cond, a, b):
        return a if cond else b

    def nn_relu_aux(i):
        cond = i < N
        if cond:
            w = src[i]
            zero = 0
            one = 1
            j = i + one
            is_neg = w < zero
            v = sel(is_neg, zero, w)
            dest[i] = v
            nn_relu_aux(j)
        else:
            return

    start = 0
    nn_relu_aux(start)
    return dest

@cocotb.test()
async def test(dut):
    hs_dut = helper.HandshakeDut(dut)
    await hs_dut.init()

    for N in [0, 5, 16]:
        print(f"testing nn_relu (N = {N})")
        src = matrix.random_matrix(1, N, lower=-100, upper=100)
        await hs_dut.assert_io(
            [N],
            [None],
            init_memory={
                "src": sum(src, []),
            },
            expected_memory={
                "dest": nn_relu(sum(src, []), N),
            },
        )
