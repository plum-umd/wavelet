#[cap(src: shrd @ i..N, dst: uniq @ i..N)]
fn copy_array<const N: usize>(i: usize, src: &[i32; N], dst: &mut [i32; N]) {
    let c = i < N;
    if c {
        let v = src[i];
        dst[i] = v;
        let one = 1;
        let j = i + one;
        copy_array::<N>(j, src, dst)
    } else {
        ()
    }
}
