void dmv(int m, int n, int A[restrict 1024], int B[restrict 1024], int Z[restrict 1024]) {
	for(int i = 0; i < m; i++) {
		int w = 0;
		for(int j = 0; j < n; j++) {
			w += A[i * n + j] * B[j];
		}
		Z[i] = w;
	}
}
