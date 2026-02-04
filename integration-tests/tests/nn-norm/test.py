import random
from .. import helper

@helper.check_equiv(
    consts=["N"],
    args=["max_val", "shift"],
    init_mem={
        "src": lambda N, **_: [random.randint(0, 255) for _ in range(N)],
        "dest": lambda N, **_: [0] * N,
    },
    tests=[
        { "N": 16, "max_val": 255, "shift": 8 },
        { "N": 25, "max_val": 1023, "shift": 10 },
    ],
)
def nn_norm(src, dest, N, max_val, shift):
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
    nn_norm_aux(0)
