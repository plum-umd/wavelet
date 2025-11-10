void dconv(const int * restrict A, int * restrict B, int * restrict Z,
	int size, int cols, int scols,
	int frows, int fcols) {

	int row = 0;
	int col = 0;
	for(int i = 0; i < size; i++) {
		int w = 0;
		int offset = row * scols + col;

		for(int j = 0; j < frows; j++) {
			for(int k = 0; k < fcols; k++) {
				w += A[offset + scols * j + k] * B[j * frows + k];
			}
		}
		Z[i] = w;

		col++;
		if(col == cols) {
			row++;
			col = 0;
		}
	}
}
