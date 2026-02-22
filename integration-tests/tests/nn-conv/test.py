import random
from sim import reference

@reference(
    (
        [random.randint(-10, 10) for _ in range(4)],
        [random.randint(0, 300) for _ in range(16)],
        [0] * 13,
        2, 2, 2, 1, 0, 16, 4, 13,
    ),
)
def nn_conv(weight, src, dest,
            weight_rows, weight_cols,
            wc_bump, wc_wr_bump,
            shift, SRC, W, OUT):
    def clamp_i16(w):
        if w < -32768:
            return -32768
        elif w > 32767:
            return 32767
        else:
            return w

    def dot_window_aux(j, row, col, src_idx, base, acc):
        if j < W:
            a = weight[j]
            src_offset = base + src_idx
            if src_offset < SRC:
                b = src[src_offset]
                prod = a * b
                sum_ = acc + prod

                col1 = col + 1
                src_idx1 = src_idx + 1
                j1 = j + 1

                hit_col_end = (col1 == weight_cols)
                if hit_col_end:
                    col2 = 0
                    row1 = row + 1
                    src_idx2 = src_idx1 + wc_bump

                    hit_row_end = (row1 == weight_rows)
                    if hit_row_end:
                        row2 = 0
                        src_idx3 = src_idx2 + wc_wr_bump
                        return dot_window_aux(
                            j1, row2, col2, src_idx3, base, sum_
                        )
                    else:
                        return dot_window_aux(
                            j1, row1, col2, src_idx2, base, sum_
                        )
                else:
                    return dot_window_aux(
                        j1, row, col1, src_idx1, base, sum_
                    )
            else:
                return acc
        else:
            return acc

    def nn_conv_aux(i):
        if i < OUT:
            w_raw = dot_window_aux(
                0, 0, 0, 0, i, 0
            )

            shifted = w_raw >> shift
            clipped = clamp_i16(shifted)
            dest[i] = clipped

            nn_conv_aux(i + 1)

    nn_conv_aux(0)
