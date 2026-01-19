void smv(const int * restrict Arow, const int * restrict Acol, 
	const int * restrict A, const int * restrict B, int * restrict Z, int m) {
	for(int i = 0; i < m; i++) {
		int start = Arow[i];
		int end = Arow[i + 1];
		int w = 0;
		for(int j = start; j < end; j++) {
			w += A[j] * B[Acol[j]];
		}
		Z[i] = w;
	}
}
