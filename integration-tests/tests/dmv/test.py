import random
from .. import helper

@helper.check_equiv(
    consts=["M", "N"],
    init_mem={
        "a": lambda M, N: [random.randint(0, 100) for _ in range(M * N)],
        "x": lambda M, N: [random.randint(0, 100) for _ in range(N)],
        "y": lambda M, N: [0 for _ in range(M)],
    },
    tests=[
        { "M": 0, "N": 0 },
        { "M": 0, "N": 1 },
        { "M": 2, "N": 3 },
        { "M": 3, "N": 2 },
        { "M": 4, "N": 4 },
        { "M": 1, "N": 5 },
        { "M": 5, "N": 1 },
    ],
)
def dmv(M, N, a, x, y):
    for i in range(M):
        acc = 0
        for j in range(N):
            acc += a[i * N + j] * x[j]
        y[i] = acc
