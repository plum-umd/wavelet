#define SHRT_MIN -32767
#define SHRT_MAX 32767

void nn_pool(
	int src[1024], int dest[1024],
	int src_size, int output_size,
	int input_rows_bump, int input_cols,
	int output_cols, int pool_size
) {
	int src_offset = 0;
	int col = 0;

	for(int i = 0; i < output_size; i++) {
		int w = SHRT_MIN;

		for(int j = 0; j < pool_size; j++) {

			for(int k = 0; k < pool_size; k++) {
				int t = src[src_offset + j * input_cols + k];
				if(t > w) w = t;
			}
		}

		dest[i] = w;
		src_offset += pool_size;
		col++;
		if(col == output_cols) {
			col = 0;
			src_offset += input_rows_bump;
		}

	}

}