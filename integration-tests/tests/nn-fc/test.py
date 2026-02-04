import random
from .. import helper

@helper.check_equiv(
    consts=["R", "C"],
    args=["shift"],
    init_mem={
        "weight": lambda R, C, **_: [random.randint(-10, 10) for _ in range(R * C)],
        "src": lambda R, C, **_: [random.randint(-100, 100) for _ in range(C)],
        "dest": lambda R, C, **_: [0] * R,
    },
    tests=[
        { "R": 4, "C": 8, "shift": 0 },
        { "R": 4, "C": 8, "shift": 4 },
        { "R": 8, "C": 16, "shift": 2 },
    ],
)
def nn_fc(weight, src, dest, R, C, shift):
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
