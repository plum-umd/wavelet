import cocotb
from .. import helper
from .. import matrix

def dither(src, R, C):
    """Same function in Python."""
    dst = [0] * (R * C)
    threshold = 256
    max_pixel = 0x1FF
    for i in range(R):
        err = 0
        row_base = i * C
        for j in range(C):
            idx = row_base + j
            out = src[idx] + err
            if out > threshold:
                dst[idx] = max_pixel
                err = out - max_pixel
            else:
                dst[idx] = 0
                err = out
    return dst

@cocotb.test()
async def test(dut):
    hs_dut = helper.HandshakeDut(dut)
    await hs_dut.init()

    for r, c in [
        (2, 3),
        (3, 2),
        (4, 4),
        (1, 5),
        (5, 1),
    ]:
        print(f"testing dithering (r = {c}, c = {c})")
        src = matrix.random_matrix(r, c, lower=0, upper=300)
        await hs_dut.assert_io(
            [r, c], [None],
            init_memory={
                "src": sum(src, []),
            },
            expected_memory={
                "dst": dither(sum(src, []), r, c),
            },
        )
