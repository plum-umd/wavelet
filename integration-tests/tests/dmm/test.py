import random
from .. import helper

@helper.check_equiv(
    consts=["M", "N", "P"],
    init_mem={
        "a": lambda M, N, P: [random.randint(0, 100) for _ in range(M * N)],
        "b": lambda M, N, P: [random.randint(0, 100) for _ in range(N * P)],
        "z": lambda M, N, P: [0 for _ in range(M * P)],
    },
    tests=[
        { "M": 0, "N": 0, "P": 0 },
        { "M": 2, "N": 3, "P": 2 },
        { "M": 3, "N": 2, "P": 4 },
        { "M": 4, "N": 4, "P": 4 },
        { "M": 1, "N": 5, "P": 3 },
        { "M": 5, "N": 1, "P": 2 },
    ],
)
def dmm(M, N, P, a, b, z):
    for i in range(M):
        for j in range(P):
            acc = 0
            for k in range(N):
                acc += a[i * N + k] * b[k * P + j]
            z[i * P + j] = acc
