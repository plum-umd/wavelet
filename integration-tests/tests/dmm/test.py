import random
from sim import reference

@reference(
    (0, 0, 0, [0], [0], [0]),
    (2, 3, 2, [random.randint(0, 100) for _ in range(6)], [random.randint(0, 100) for _ in range(6)], [0 for _ in range(4)]),
    (3, 2, 4, [random.randint(0, 100) for _ in range(6)], [random.randint(0, 100) for _ in range(8)], [0 for _ in range(12)]),
    (4, 4, 4, [random.randint(0, 100) for _ in range(16)], [random.randint(0, 100) for _ in range(16)], [0 for _ in range(16)]),
    (1, 5, 3, [random.randint(0, 100) for _ in range(5)], [random.randint(0, 100) for _ in range(15)], [0 for _ in range(3)]),
    (5, 1, 2, [random.randint(0, 100) for _ in range(5)], [random.randint(0, 100) for _ in range(2)], [0 for _ in range(10)]),
)
def dmm(M, N, P, a, b, z):
    for i in range(M):
        for j in range(P):
            acc = 0
            for k in range(N):
                acc += a[i * N + k] * b[k * P + j]
            z[i * P + j] = acc
