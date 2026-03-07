void nn_relu(int src[restrict 1024], int dest[restrict 1024], int size) {
	for (int i = 0; i < size; i++) {
		int w = src[i];
		if (w < 0) w = 0;
		dest[i] = w;
	}
}