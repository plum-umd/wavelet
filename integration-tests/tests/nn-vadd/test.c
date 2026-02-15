void nn_vadd(int weight[1024], int src[1024], int dest[1024], int size) {
	for(int i = 0; i < size; i++) {
		dest[i] = src[i] + weight[i];
	}
}