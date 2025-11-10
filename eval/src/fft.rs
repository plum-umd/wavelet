fn fft_inner_aux<const N: usize, const TW: usize>(
    l: usize,
    k: usize,
    j: usize,
    real: &mut [i32; N],
    imag: &mut [i32; N],
    real_twiddle: &[i32; TW],
    imag_twiddle: &[i32; TW],
    size: usize,
    step: usize,
    stride: usize,
    strided_step: usize,
    ls_stride: usize,
    theta: usize,
) {
    let cond = k < size;
    if cond {
        // Twiddle for this butterfly (constant across inner loop for fixed j)
        let theta_idx = j + theta;
        let wr = real_twiddle[theta_idx];
        let wi = imag_twiddle[theta_idx];

        // Indices
        let base = j * stride + l * strided_step;
        let pair = base + ls_stride;

        // Top/second element of the butterfly at (base + Ls_stride)
        let re2 = real[pair];
        let im2 = imag[pair];
        let tr = wr * re2 - wi * im2;
        let ti = wr * im2 + wi * re2;

        // Bottom/first element at base
        let re1 = real[base];
        let im1 = imag[base];

        // Write results
        real[pair] = re1 - tr;
        imag[pair] = im1 - ti;
        real[base] = re1 + tr;
        imag[base] = im1 + ti;

        // Next inner iteration
        let one = 1usize;
        let l1 = l + one;
        let k1 = k + step;
        fft_inner_aux::<N, TW>(
            l1,
            k1,
            j,
            real,
            imag,
            real_twiddle,
            imag_twiddle,
            size,
            step,
            stride,
            strided_step,
            ls_stride,
            theta,
        )
    } else {
        ()
    }
}

fn fft_outer_aux<const N: usize, const TW: usize>(
    j: usize,
    real: &mut [i32; N],
    imag: &mut [i32; N],
    real_twiddle: &[i32; TW],
    imag_twiddle: &[i32; TW],
    size: usize,
    stride: usize,
    step: usize,
    ls: usize,
    theta: usize,
    strided_step: usize,
    ls_stride: usize,
) {
    let cond = j < ls;
    if cond {
        // Inner loop over k (with l as the iteration counter)
        fft_inner_aux::<N, TW>(
            0, // l
            j, // k starts at j
            j,
            real,
            imag,
            real_twiddle,
            imag_twiddle,
            size,
            step,
            stride,
            strided_step,
            ls_stride,
            theta,
        );

        // Next j
        let one = 1usize;
        let j1 = j + one;
        fft_outer_aux::<N, TW>(
            j1,
            real,
            imag,
            real_twiddle,
            imag_twiddle,
            size,
            stride,
            step,
            ls,
            theta,
            strided_step,
            ls_stride,
        )
    } else {
        ()
    }
}

pub fn fft<const N: usize, const TW: usize>(
    real: &mut [i32; N],
    imag: &mut [i32; N],
    real_twiddle: &[i32; TW],
    imag_twiddle: &[i32; TW],
    size: usize,
    stride: usize,
    step: usize,
    ls: usize,
    theta: usize,
    strided_step: usize,
    ls_stride: usize,
) {
    fft_outer_aux::<N, TW>(
        0,
        real,
        imag,
        real_twiddle,
        imag_twiddle,
        size,
        stride,
        step,
        ls,
        theta,
        strided_step,
        ls_stride,
    )
}
