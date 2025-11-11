use dfx_macros::cap;

#[cap(weight: shrd @ i..N, src: shrd @ i..N, dest: uniq @ i..N)]
pub fn nn_vadd_aux<const N: usize>(
    i: usize,
    weight: &[u32; N],
    src: &[u32; N],
    dest: &mut [u32; N],
) {
    let cond = i < N;
    if cond {
        let w = weight[i];
        let s = src[i];
        let sum = w + s;
        dest[i] = sum;

        let one = 1;
        let j = i + one;
        nn_vadd_aux::<N>(j, weight, src, dest)
    } else {
        ()
    }
}

#[cap(weight: shrd @ 0..N, src: shrd @ 0..N, dest: uniq @ 0..N)]
pub fn nn_vadd<const N: usize>(weight: &[u32; N], src: &[u32; N], dest: &mut [u32; N]) {
    let start = 0;
    nn_vadd_aux::<N>(start, weight, src, dest)
}
