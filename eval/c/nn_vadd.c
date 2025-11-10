void nn_vadd(int * weight, int * src, int * dest, int size) {
	for(int i = 0; i < size; i++) {
		dest[i] = src[i] + weight[i];
	}
}