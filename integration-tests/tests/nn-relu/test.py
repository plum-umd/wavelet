import random
from .. import helper

@helper.check_equiv(
    consts=["N"],
    init_mem={
        "src": lambda N: [random.randint(-100, 100) for _ in range(N)],
        "dest": lambda N: [0] * N,
    },
    tests=[
        { "N": 0 },
        { "N": 5 },
        { "N": 16 },
    ],
)
def nn_relu(src, dest, N):
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
