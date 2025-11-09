#[cap(B: uniq @ j..N)]
fn war_bad<const N: usize>(j: usize, B: &mut [i32; N]) {
    let one = 1;
    let n_minus_one = N - one;
    let cond = j < n_minus_one;
    if cond {
        let jp1 = j + one;
        let v = B[jp1];
        B[j] = v;
        let k = j + one;
        war_bad::<N>(k, B)
    } else {
        ()
    }
}
