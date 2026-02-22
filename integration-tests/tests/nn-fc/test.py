import random
from sim import reference

@reference(
    ([random.randint(-10, 10) for _ in range(32)], [random.randint(-100, 100) for _ in range(8)], [0] * 4, 0, 4, 8),
    ([random.randint(-10, 10) for _ in range(32)], [random.randint(-100, 100) for _ in range(8)], [0] * 4, 4, 4, 8),
    ([random.randint(-10, 10) for _ in range(128)], [random.randint(-100, 100) for _ in range(16)], [0] * 8, 2, 8, 16),
)
def nn_fc(weight, src, dest, shift, R, C):
    def row_dot(i, j, acc):
        cond = j < C
        if cond:
            base = i * C
            idx = base + j
            s_val = src[j]
            w_val = weight[idx]
            prod = s_val * w_val
            new_acc = acc + prod
            one = 1
            next_j = j + one
            return row_dot(i, next_j, new_acc)
        else:
            return acc

    def clamp_i16(w):
        min_val = -32768
        below = w < min_val
        if below:
            return min_val
        else:
            max_val = 32767
            above = max_val < w
            if above:
                return max_val
            else:
                return w

    def rec_rows(i):
        cond = i < R
        if cond:
            dot = row_dot(i, 0, 0)
            shifted = dot >> shift
            clamped = clamp_i16(shifted)
            dest[i] = clamped
            one = 1
            next_i = i + one
            rec_rows(next_i)

    rec_rows(0)
