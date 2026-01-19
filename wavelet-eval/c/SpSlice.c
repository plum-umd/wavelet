void SpSlice(const int* restrict ia, const int* restrict ij, const int* restrict ii,
        const int* restrict idxj, const int* restrict idxi,
        int rows, int* restrict out)
{
    for (int row = 0; row < rows; row++) {
        int rowst = ii[row];
        int rowen = ii[row+1];
        int idxst = idxi[row];
        int idxen = idxi[row+1];
        int im = rowst;
        int ix = idxst;
        int new_im = im;
        int new_ix = ix;
        while (im < rowen && ix < idxen) {
            if (ij[im] == idxj[ix]) {
                out[ix] = ia[im];
            }
            if (ij[im] <= idxj[ix]) {
                new_im = im + 1;
                new_ix = ix;
            }
            if (ij[im] >= idxj[ix]) {
                new_im = im;
                new_ix = ix + 1;
            }
            im = new_im;
            ix = new_ix;
        }
    }
}
