void Dither(int* restrict src, int* dst, int rows, int cols)
{
    for (int i = 0; i < rows; i++) {
        int err = 0;
        int pixel;
        for (int j = 0; j < cols; j++) {
            int out = src[i*cols+j] + err;
            if (out > 256) {
                pixel = 0x1FF;
                err = out - pixel;
            }
            else {
                pixel = 0;
                err = out;
            }
            dst[i*cols+j] = pixel;
        }
    }
}
