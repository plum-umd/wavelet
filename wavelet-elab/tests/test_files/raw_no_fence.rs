#[cap(A: uniq @ j-1..N)]
fn raw_bad<const N: usize>(j: usize, A: &mut [i32; N]) {
    let one = 1;
    let cond_hi = j < N;
    let cond_lo = one <= j;
    let cond = cond_hi && cond_lo;
    if cond {
        let jm1 = j - one;
        let v = A[jm1];
        A[j] = v;
        let k = j + one;
        raw_bad::<N>(k, A)
    } else {
        ()
    }
}
