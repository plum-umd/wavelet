import random
from .. import helper

@helper.check_equiv(
    consts=["R", "C"],
    init_mem={
        "src": lambda R, C: [random.randint(0, 300) for _ in range(R * C)],
        "dst": lambda R, C: [0] * (R * C),
    },
    tests=[
        { "R": 2, "C": 3 },
        { "R": 3, "C": 2 },
        { "R": 4, "C": 4 },
        { "R": 1, "C": 5 },
        { "R": 5, "C": 1 },
    ],
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
