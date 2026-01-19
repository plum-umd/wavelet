#[cap(A: uniq @ i..N)]
fn increment_bad<const N: usize>(i: usize, A: &mut [i32; N]) {
    let c = i < N;
    if c {
        let v = A[i];
        let one = 1;
        let new_v = v + one;
        A[i] = new_v;
        let j = i + one;
        increment_bad::<N>(j, A)
    } else {
        ()
    }
}
