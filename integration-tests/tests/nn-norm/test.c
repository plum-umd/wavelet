void nn_norm(int src[1024], int dest[1024], int size, int max, int shift) {
	for(int i = 0; i < size; i++) {
		dest[i] = (src[i] * max) >> shift;
	}
}