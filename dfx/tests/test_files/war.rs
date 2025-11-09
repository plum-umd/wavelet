#[cap(B: uniq @ j..N)]
fn war<const N: usize>(j: usize, B: &mut [i32; N]) {
    let one = 1;
    let n_minus_one = N - one;
    let cond = j < n_minus_one;
    if cond {
        let jp1 = j + one;
        let v = B[jp1];
        fence!();
        B[j] = v;
        let k = j + one;
        war::<N>(k, B)
    } else {
        ()
    }
}
