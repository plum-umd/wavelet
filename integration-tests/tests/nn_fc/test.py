import cocotb
from .. import helper
from .. import matrix

def nn_fc(weight, src, R, C, shift):
    dest = [0] * R

    def row_dot(i, j, acc):
        cond = j < C
        if cond:
            base = i * C
            idx = base + j
            s_val = src[j]
            w_val = weight[idx]
            prod = s_val * w_val
            new_acc = acc + prod
            one = 1
            next_j = j + one
            return row_dot(i, next_j, new_acc)
        else:
            return acc

    def clamp_i16(w):
        min_val = -32768
        below = w < min_val
        if below:
            return min_val
        else:
            max_val = 32767
            above = max_val < w
            if above:
                return max_val
            else:
                return w

    def rec_rows(i):
        cond = i < R
        if cond:
            dot = row_dot(i, 0, 0)
            shifted = dot >> shift
            clamped = clamp_i16(shifted)
            dest[i] = clamped
            one = 1
            next_i = i + one
            rec_rows(next_i)
        else:
            return

    start = 0
    rec_rows(start)
    return dest

@cocotb.test()
async def test(dut):
    hs_dut = helper.HandshakeDut(dut)
    await hs_dut.init()

    for R, C, shift in [
        (4, 8, 0),
        (4, 8, 4),
        (8, 16, 2),
    ]:
        print(f"testing nn_fc (rows = {R}, cols = {C}, shift = {shift})")
        weight = matrix.random_matrix(R, C, lower=-10, upper=10)
        src = matrix.random_matrix(1, C, lower=-100, upper=100)
        await hs_dut.assert_io(
            [shift, R, C],
            [None],
            init_memory={
                "weight": sum(weight, []),
                "src": sum(src, []),
            },
            expected_memory={
                "dest": nn_fc(sum(weight, []), sum(src, []), R, C, shift),
            },
        )
