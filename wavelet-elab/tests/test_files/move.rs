#[cap(src: uniq @ i..N, dst: uniq @ i..N)]
fn move_fn<const N: usize>(i: usize, src: &[i32; N], dst: &mut [i32; N]) {
    let c = i < N;
    if c {
        let v = src[i];
        dst[i] = v;
        let one = 1;
        let zero = 0;
        fence!();
        src[i] = zero;
        let j = i + one;
        move_fn::<N>(j, src, dst)
    } else {
        ()
    }
}
