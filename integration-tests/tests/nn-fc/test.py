from sim import reference

@reference(
    ([-10, -7, 7, -2, 10, 0, -7, -1, 3, -5, 4, -10, -2, 6, -5, 6, -7, 10, -1, 10, 6, 9, -4, -6, 1, -5, 7, 6, -10, 9, 0, 5], [-96, -72, -8, -22, -39, -86, -39, 45], [0] * 4, 0, 4, 8),
    ([-8, -8, 5, -8, 7, -6, -6, 5, 7, -5, -2, 6, 9, 3, -4, 7, -4, -1, 2, 10, 1, 4, 6, 4, -7, -3, -3, -8, 0, -10, 8, 7], [-42, 50, -44, -99, -82, 81, 61, -85], [0] * 4, 4, 4, 8),
    ([-3, -8, -9, 0, -8, 6, -3, -2, 5, -4, 7, -6, 8, 8, 5, -3, 5, 3, -4, -7, -7, 3, 1, 3, 3, 4, -9, 10, 10, -7, -9, 2, 0, -7, -3, -4, -4, 7, 4, -6, 3, -5, -2, 4, -3, -8, 4, 7, -7, -9, 10, 7, -10, -8, -3, -5, 3, 5, 5, -4, 2, -9, -5, 2, -10, 2, -2, 4, -1, 3, 7, 5, -6, -4, -1, -4, -9, 8, 7, -9, 0, -9, -9, 8, 5, 6, 6, -5, -9, 6, -8, -5, -8, 9, -8, -3, 2, -7, 8, -3, 8, 9, -9, 9, -8, 3, 8, 8, 6, 0, -2, -4, 0, -3, -2, 2, -6, 10, -1, 4, 0, -8, -10, 4, 9, 8, -7, -8], [37, -46, 29, -33, -67, -11, -83, -38, -6, -28, -60, 12, 39, 80, -23, 56], [0] * 8, 2, 8, 16),
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
