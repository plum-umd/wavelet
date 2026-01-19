void dmv(const int * restrict A, const int * restrict B, 
	int * restrict Z, int m, int n) {
	for(int i = 0; i < m; i++) {
		int w = 0;
		for(int j = 0; j < n; j++) {
			w += A[i * n + j] * B[j];
		}
		Z[i] = w;
	}
}
