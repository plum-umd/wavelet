#[cap(src: shrd @ i..N, dest: uniq @ i..N)]
fn nn_relu_aux<const N: usize>(i: usize, src: &[i32; N], dest: &mut [i32; N]) {
    let cond = i < N;
    if cond {
        let w = src[i];
        let zero = 0;
        let one = 1;
        let j = i + one;
        let is_neg = w < zero;
        if is_neg {
            dest[i] = zero;
            nn_relu_aux::<N>(j, src, dest)
        } else {
            dest[i] = w;
            nn_relu_aux::<N>(j, src, dest)
        }
    } else {
        ()
    }
}

#[cap(src: shrd @ 0..N, dest: uniq @ 0..N)]
fn nn_relu<const N: usize>(src: &[i32; N], dest: &mut [i32; N]) {
    let start = 0;
    nn_relu_aux::<N>(start, src, dest)
}
