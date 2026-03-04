from sim import reference

@reference(
    (2, 3, [299, 46, 30, 99, 101, 8], [0] * 6),
    (3, 2, [286, 139, 107, 114, 137, 15], [0] * 6),
    (4, 4, [279, 98, 163, 234, 137, 196, 216, 170, 209, 103, 88, 38, 282, 50, 50, 242], [0] * 16),
    (1, 5, [72, 294, 62, 204, 169], [0] * 5),
    (5, 1, [221, 70, 155, 226, 78], [0] * 5),
)
def dither(R, C, src, dst):
    threshold = 256
    max_pixel = 0x1FF

    for i in range(R):
        err = 0
        row_base = i * C

        for j in range(C):
            idx = row_base + j
            out = src[idx] + err

            if out > threshold:
                dst[idx] = max_pixel
                err = out - max_pixel
            else:
                dst[idx] = 0
                err = out
