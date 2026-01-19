void nn_relu(int * src, int * dest, int size) {

	int * src_ptr = src;
	int * dest_ptr = dest;

	for(int i = 0; i < size; i++) {
		int w = *src_ptr++;
		if(w < 0) w = 0;
		*dest_ptr++ = w;
	}
}