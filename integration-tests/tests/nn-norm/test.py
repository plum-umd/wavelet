from sim import reference

@reference(
    ([4, 153, 53, 68, 135, 59, 54, 79, 139, 144, 107, 175, 104, 135, 250, 128], [0] * 16, 255, 8, 16),
    ([26, 47, 216, 141, 22, 1, 170, 66, 134, 82, 226, 218, 4, 57, 38, 76, 18, 189, 75, 220, 65, 21, 157, 186, 20], [0] * 25, 1023, 10, 25),
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
