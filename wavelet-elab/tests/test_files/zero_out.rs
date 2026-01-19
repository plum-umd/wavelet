#[cap(A: uniq @ i..N)]
fn zero_out<const N: usize>(i: usize, A: &mut [i32; N]) {
    let c = i < N;
    if c {
        let zero = 0;
        A[i] = zero;
        let one = 1;
        let j = i + one;
        zero_out::<N>(j, A)
    } else {
        ()
    }
}
