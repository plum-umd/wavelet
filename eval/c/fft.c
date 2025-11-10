void fft(
	int * restrict real,
	int * restrict imag,
	const int * restrict real_twiddle,
	const int * restrict imag_twiddle,
	int size, int stride, int step,
	int Ls, int theta,
	int strided_step, int Ls_stride) {

	for(int j = 0; j < Ls; j++) {
		int theta_idx = j + theta;
		int wr = real_twiddle[theta_idx];
		int wi = imag_twiddle[theta_idx];

		for(int k = j, l = 0; k < size; k += step, l++) {
			int re = real[j * stride + l * strided_step + Ls_stride];
			int im = imag[j * stride + l * strided_step + Ls_stride];
			int tr = wr * re - wi * im;
			int ti = wr * im + wi * re;

			re = real[j * stride + l * strided_step];
			im = imag[j * stride + l * strided_step];
			real[j * stride + l * strided_step + Ls_stride] = re - tr;
			imag[j * stride + l * strided_step + Ls_stride] = im - ti;
			real[j * stride + l * strided_step] = re + tr;
			imag[j * stride + l * strided_step] = im + ti;
		}
	}
}
