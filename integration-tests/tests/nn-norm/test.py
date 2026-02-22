import random
from sim import reference

@reference(
    ([random.randint(0, 255) for _ in range(16)], [0] * 16, 255, 8, 16),
    ([random.randint(0, 255) for _ in range(25)], [0] * 25, 1023, 10, 25),
)
def nn_norm(src, dest, max_val, shift, N):
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
