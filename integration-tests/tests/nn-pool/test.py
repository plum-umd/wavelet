import random
from sim import reference

@reference(
    ([random.randint(-100, 100) for _ in range(16)], [0] * 4, 16, 4, 2, 4, 2, 2),
    ([random.randint(-100, 100) for _ in range(36)], [0] * 9, 36, 9, 4, 6, 3, 2),
)
def nn_pool(src, dest, SRC, OUT,
            input_rows_bump,
            input_cols,
            output_cols,
            pool_size):
    def sel(cond, a, b):
        return a if cond else b

    def pool_k_aux(k, src_offset, j, w):
        cond = k < pool_size
        if cond:
            j_mul_cols = j * input_cols
            idx_base = src_offset + j_mul_cols
            idx = idx_base + k
            safe = idx < SRC
            if safe:
                t = src[idx]
                cond1 = w < t
                one = 1
                k1 = k + one
                tw = sel(cond1, t, w)
                return pool_k_aux(k1, src_offset, j, tw)
            else:
                return w
        else:
            return w

    def pool_j_aux(j, src_offset, w):
        cond = j < pool_size
        if cond:
            w_after_k = pool_k_aux(0, src_offset, j, w)
            one = 1
            j1 = j + one
            return pool_j_aux(j1, src_offset, w_after_k)
        else:
            return w

    def nn_pool_aux(i, src_offset, col):
        cond = i < OUT
        if cond:
            w0 = -32767
            w = pool_j_aux(0, src_offset, w0)
            dest[i] = w

            one = 1
            i1 = i + one

            src_offset_right = src_offset + pool_size
            col1 = col + one
            end_of_row = col1 == output_cols

            if end_of_row:
                new_col = 0
                src_offset_next_row = src_offset_right + input_rows_bump
                nn_pool_aux(i1, src_offset_next_row, new_col)
            else:
                nn_pool_aux(i1, src_offset_right, col1)
        else:
            return

    start_i = 0
    start_off = 0
    start_col = 0
    nn_pool_aux(start_i, start_off, start_col)
