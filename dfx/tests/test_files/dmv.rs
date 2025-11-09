#[cap(a: shrd @ i..MN, x: shrd @ j..N)]
fn cal_dot_product<const MN: usize, const N: usize>(
    j: usize,
    i: usize,
    a: &[u32; MN],
    x: &[u32; N],
    acc: u32,
) -> u32 {
    let cond = j < N;
    if cond {
        let idx = i + j;
        let a_val = a[idx];
        let x_val = x[j];
        let prod = a_val * x_val;
        let new_acc = acc + prod;
        let one = 1;
        let next = j + one;
        cal_dot_product::<MN, N>(next, i, a, x, new_acc)
    } else {
        acc
    }
}

#[cap(a: shrd @ idx..MN, x: shrd @ 0..N, y: uniq @ idx..M)]
fn mv_mul<const M: usize, const N: usize, const MN: usize>(
    idx: usize,
    a: &[u32; MN],
    x: &[u32; N],
    y: &mut [u32; M],
) {
    let cond = idx < M;
    if cond {
        let dot = cal_dot_product::<MN, N>(0, idx, a, x, 0);
        y[idx] = dot;
        let one = 1;
        let next = idx + one;
        mv_mul::<M, N, MN>(next, a, x, y)
    } else {
        ()
    }
}

#[cap(a: shrd @ 0..MN, x: shrd @ 0..N, y: uniq @ 0..M)]
fn dmv<const M: usize, const N: usize, const MN: usize>(
    a: &[u32; MN],
    x: &[u32; N],
    y: &mut [u32; M],
) {
    let start = 0;
    mv_mul::<M, N, MN>(start, a, x, y)
}
