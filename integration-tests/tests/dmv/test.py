import random
from sim import reference

@reference(
    (0, 0, [], [], []),
    (0, 1, [], [random.randint(0, 100) for _ in range(1)], []),
    (2, 3, [random.randint(0, 100) for _ in range(6)], [random.randint(0, 100) for _ in range(3)], [0 for _ in range(2)]),
    (3, 2, [random.randint(0, 100) for _ in range(6)], [random.randint(0, 100) for _ in range(2)], [0 for _ in range(3)]),
    (4, 4, [random.randint(0, 100) for _ in range(16)], [random.randint(0, 100) for _ in range(4)], [0 for _ in range(4)]),
    (1, 5, [random.randint(0, 100) for _ in range(5)], [random.randint(0, 100) for _ in range(5)], [0 for _ in range(1)]),
    (5, 1, [random.randint(0, 100) for _ in range(5)], [random.randint(0, 100) for _ in range(1)], [0 for _ in range(5)]),
)
def dmv(M, N, a, x, y):
    for i in range(M):
        acc = 0
        for j in range(N):
            acc += a[i * N + j] * x[j]
        y[i] = acc
