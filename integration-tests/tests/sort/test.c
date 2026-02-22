void sort(int A[1024], int Z[1024], int even_count, int size) {
	int count = even_count;
	
	for(int i = 0; i < 32; i++) {
		int odd = i & 0x1;
		int idx0 = 0;
		int idx1 = count;
		int next_count = 0;

		for(int j = 0; j < size; j++) {
			int v = odd ? Z[j] : A[j];
			int o = (v >> i) & 0x1;
			next_count += (v & (1 << (i + 1))) == 0x0;

			if (o) {
				if (odd) {
					A[idx1++] = v;
				} else {
					Z[idx1++] = v;
				}
			} else {
				if (odd) {
					A[idx0++] = v;
				} else {
					Z[idx0++] = v;
				}
			}
		}

    	count = next_count;
	}
}
