void nn_norm(int src[restrict 1024], int dest[restrict 1024], int max, int shift, int size) {
	for(int i = 0; i < size; i++) {
		dest[i] = (src[i] * max) >> shift;
	}
}