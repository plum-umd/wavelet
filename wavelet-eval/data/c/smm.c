void smm(int * restrict Arow, int * restrict Acol, 
	int * restrict A, int * restrict Brow, int * restrict Bcol, 
	int * restrict B, int * restrict Z, int rows, int cols) {

	int *dest_ptr = Z; 
	for(int i = 0; i < rows; i++) {
		int j_start = Arow[i];
		int j_end = Arow[i + 1];
		for(int j = j_start; j < j_end; j++) {
			int row = Acol[j];	
			int k_start = Brow[row];
			int k_end = Brow[row + 1];
			int f = A[j];
			for(int k = k_start; k < k_end; k++) {
				int w = f * B[k];
				int *d = dest_ptr + Bcol[k];
				*d += w;
			}
		}
		dest_ptr += cols;
	}
}
