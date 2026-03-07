void sort(int A[restrict 1024], int Z[restrict 1024], int even_count, int size) {
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

			int idx = (o) ? idx1++ : idx0++;

			if (idx < size) dst[idx] = v;
		}

    	count = next_count;
	}
}
