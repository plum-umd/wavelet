void SpMSpMd(int * Y, int R, int C,
        int * restrict aa, int * restrict aj, int * restrict ai,
        int * restrict ba, int * restrict bj, int * restrict bi) {
    for (int i = 0; i < R; i++) {
        int ARS = ai[i];
        int ARE = ai[i+1];

        for (int j = 0; j < C; j++) {
            int BCS = bi[j];
            int BCE = bi[j+1];

            int iA = ARS;
            int iB = BCS;

            int new_iA = iA;
            int new_iB = iB;

            int acc = 0;

            while (iA < ARE && iB < BCE) {
                if (aj[iA] == bj[iB]) {
                    acc += aa[iA] * ba[iB];
                }
                if (aj[iA] <= bj[iB]) {
                    new_iA = iA + 1;
                }
                if (aj[iA] >= bj[iB]) {
                    new_iB = iB + 1;
                }

                iA = new_iA;
                iB = new_iB;
            }

            Y[i*C+j] = acc;
        }
    }
    return;
}
