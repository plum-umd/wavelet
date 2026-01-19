void sort(int * A, int * Z, int size, int even_count) {
	int count = even_count;
	for(int i = 0; i < 32; i++) {
		int odd = i & 0x1;
		int * src = (odd) ? Z : A;
		int * dst = (odd) ? A : Z;

		int idx0 = 0;
		int idx1 = count;
		int next_count = 0;

		for(int j = 0; j < size; j++) {
			int v = src[j];
			int o = (v >> i) & 0x1;
			next_count += (v & (1 << (i + 1))) == 0x0;

			if(o) dst[idx1++] = v;
			else dst[idx0++] = v;
		}

    	count = next_count;
	}
}
