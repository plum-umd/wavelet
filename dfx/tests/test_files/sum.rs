#[cap(A: shrd @ i..N)]
fn sum<const N: usize>(i: usize, a: i32, A: &[i32; N]) -> i32 {
    let c = i < N;
    if c {
        let val = A[i];
        let one = 1;
        let j = i + one;
        let new_a = a + val;
        sum::<N>(j, new_a, A)
    } else {
        a
    }
}
