#[cap(C: uniq @ j..N)]
fn waw<const N: usize>(j: usize, C: &mut [i32; N]) {
    let one = 1;
    let n_minus_one = N - one;
    let cond = j < n_minus_one;
    if cond {
        C[j] = j;
        let jp1 = j + one;
        let five = 5;
        C[jp1] = five;
        fence!();
        let k = j + one;
        waw::<N>(k, C)
    } else {
        ()
    }
}
