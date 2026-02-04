import random
from .. import helper

@helper.check_equiv(
    consts=["N"],
    init_mem={
        "weight": lambda N: [random.randint(-100, 100) for _ in range(N)],
        "src": lambda N: [random.randint(-100, 100) for _ in range(N)],
        "dest": lambda N: [0] * N,
    },
    tests=[
        { "N": 0 },
        { "N": 5 },
        { "N": 10 },
    ],
)
def nn_vadd(weight, src, dest, N):
    for i in range(N):
        dest[i] = weight[i] + src[i]
