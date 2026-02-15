import random
from sim import reference

@reference(
    (2, 3, [random.randint(0, 300) for _ in range(6)], [0] * 6),
    (3, 2, [random.randint(0, 300) for _ in range(6)], [0] * 6),
    (4, 4, [random.randint(0, 300) for _ in range(16)], [0] * 16),
    (1, 5, [random.randint(0, 300) for _ in range(5)], [0] * 5),
    (5, 1, [random.randint(0, 300) for _ in range(5)], [0] * 5),
)
def dither(R, C, src, dst):
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
