#define SHRT_MIN -32767
#define SHRT_MAX 32767

void nn_conv(
	int * restrict weight, int * restrict src, int * restrict dest,
	int output_cols,
	int weight_rows, int weight_cols,
	int weight_size, int wc_bump, int wc_wr_bump,
	int shift) {

	int ocol = 0;

	for(int i = 0; i < output_cols; i++) {
		int w = 0;
		int row = 0;
		int col = 0;
		int src_idx = 0;

		for(int j = 0; j < weight_size; j++) {
			w += weight[j] * src[i + src_idx];

			col++;
			src_idx++;
			if(col == weight_cols) {
				col = 0;
				row++;
				src_idx += wc_bump;
				if(row == weight_rows) {
					row = 0;
					src_idx += wc_wr_bump;
				}
			}
		}

		w >>= shift;
		if(w < SHRT_MIN) w = SHRT_MIN;
		if(w > SHRT_MAX) w = SHRT_MAX;

		dest[i] = w;
	}

}