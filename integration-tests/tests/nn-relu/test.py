from sim import reference

@reference(
    ([], [], 0),
    ([2, 73, 37, -16, -93], [0] * 5, 5),
    ([-71, -34, -55, 48, -33, -91, -73, 52, 11, -12, 86, -20, 11, 55, 30, -71], [0] * 16, 16),
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
