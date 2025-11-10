void dmm(int * restrict A, int * restrict B, int * restrict Z, int m, int n, int p) {
	int dest_idx = 0;
	int *filter_ptr = A;
	for(int i = 0; i < m; i++) {
		for(int j = 0; j < p; j++) {
			int w = 0;
			int src_idx = j;
			for(int k = 0; k < n; k++) {
				w += filter_ptr[k] * B[src_idx];
				src_idx += p;
			}
			Z[dest_idx++] = w;
		}
		filter_ptr += n;
	}
}
