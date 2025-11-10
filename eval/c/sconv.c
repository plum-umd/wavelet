void sconv(const int * restrict A, const int * restrict Brow, 
	const int * restrict Bcol, const int * restrict B, int * restrict Z, 
	int rowBound, int colBound, int n, int total_elements) {

	int row = 0;
	for(int i = 0; i < rowBound; i++) {
		int offset = i * n;
		for(int j = 0; j < colBound; j++) {

			int w = 0;
			for(int k = 0; k < total_elements; k++) {
				int frow = Brow[k];
				int fcol = Bcol[k];
				 w += B[k] * A[offset + frow * n + fcol];
			}

			Z[row + j] = w;
			offset++;
		}
		row += colBound;
	}
}
