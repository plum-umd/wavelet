#define SHRT_MIN -32767
#define SHRT_MAX 32767

void nn_fc(int weight[1024], int src[1024], int dest[1024],
	int rows, int cols, int shift) {

	for(int i = 0; i < rows; i++) {
		int w = 0;

		for(int j = 0; j < cols; j++) {
			int s = src[j];
			int f = weight[i * cols + j];
			w += s * f;
		}

		w >>= shift;
		if(w < SHRT_MIN) w = SHRT_MIN;
		if(w > SHRT_MAX) w = SHRT_MAX;

		dest[i] = w;
	}

}