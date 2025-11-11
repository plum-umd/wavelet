use dfx_macros::cap;

#[cap(src: shrd @ i..N, dest: uniq @ i..N)]
fn nn_norm_aux<const N: usize>(
    i: usize,
    src: &[u32; N],
    dest: &mut [u32; N],
    max: u32,
    shift: u32,
) {
    let cond = i < N;
    if cond {
        let v = src[i];
        let prod = v * max;
        let scaled = prod >> shift;
        dest[i] = scaled;

        let one = 1;
        let j = i + one;
        nn_norm_aux::<N>(j, src, dest, max, shift)
    } else {
        ()
    }
}

#[cap(src: shrd @ 0..N, dest: uniq @ 0..N)]
fn nn_norm<const N: usize>(src: &[u32; N], dest: &mut [u32; N], max: u32, shift: u32) {
    let start = 0;
    nn_norm_aux::<N>(start, src, dest, max, shift)
}
