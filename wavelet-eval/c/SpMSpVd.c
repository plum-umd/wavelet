void SpMSpVd(int* restrict Y, int R, int C,
    const int* restrict aa, const int* restrict aj, const int* restrict ai,
    const int* restrict ba, const int* restrict bj, int bnnz)
{
    for (int i = 0; i < R; i++) {
        int ARS = ai[i];
        int ARE = ai[i+1];

        int BCS = 0;
        int BCE = bnnz;

        int iA = ARS;
        int iB = BCS;

        int new_iA = iA;
        int new_iB = iB;

        int acc = 0;

        int a_col, b_col;
        int a_val, b_val;

        while (iA < ARE && iB < BCE) {
            a_col = aj[iA];
            b_col = bj[iB];
            a_val = aa[iA];
            b_val = ba[iB];

            if (a_col == b_col) {
                acc += a_val * b_val;
            }
            if (a_col <= b_col) {
                new_iA = iA + 1;
            }
            if (a_col >= b_col) {
                new_iB = iB + 1;
            }

            iA = new_iA;
            iB = new_iB;
        }

        Y[i] = acc;
    }
}
