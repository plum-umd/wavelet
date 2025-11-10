void nn_norm(int * src, int * dest,
	int size, int max, int shift) {

	int * src_ptr = src;
	int * dest_ptr = dest;

	for(int i = 0; i < size; i++) {
		*dest_ptr++ = (*src_ptr++ * max) >> shift;
	}
}