import random
from sim import reference

@reference(
    ([], [], 0),
    ([random.randint(-100, 100) for _ in range(5)], [0] * 5, 5),
    ([random.randint(-100, 100) for _ in range(16)], [0] * 16, 16),
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
