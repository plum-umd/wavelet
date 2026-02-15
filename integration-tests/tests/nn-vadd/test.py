import random
from sim import reference

@reference(
    ([], [], [], 0),
    ([random.randint(-100, 100) for _ in range(5)], [random.randint(-100, 100) for _ in range(5)], [0] * 5, 5),
    ([random.randint(-100, 100) for _ in range(10)], [random.randint(-100, 100) for _ in range(10)], [0] * 10, 10),
)
def nn_vadd(weight, src, dest, N):
    for i in range(N):
        dest[i] = weight[i] + src[i]
