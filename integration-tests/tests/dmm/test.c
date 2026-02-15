void dmm(int m, int n, int p, int A[1024], int B[1024], int Z[1024]) {
	int dest_idx = 0;
	int filter_idx = 0;
	for(int i = 0; i < m; i++) {
		for(int j = 0; j < p; j++) {
			int w = 0;
			int src_idx = j;
			for(int k = 0; k < n; k++) {
				w += A[filter_idx + k] * B[src_idx];
				src_idx += p;
			}
			Z[dest_idx++] = w;
		}
		filter_idx += n;
	}
}
