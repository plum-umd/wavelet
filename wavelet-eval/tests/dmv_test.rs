#![feature(generic_const_exprs)]

use dfx_macros::cap;

#[cap(a: shrd @ i*N..i*N + N, x: shrd @ j..N)]
fn cal_dot_product<const M: usize, const N: usize>(
    j: usize,
    i: usize,
    a: &[u32; { M * N }],
    x: &[u32; N],
    acc: u32,
) -> u32 {
    let cond = j < N;
    if cond {
        let idx_mul = i * N;
        let idx = idx_mul + j;
        let a_val = a[idx];
        let x_val = x[j];
        let prod = a_val * x_val;
        let new_acc = acc + prod;
        let one = 1;
        let next = j + one;
        cal_dot_product::<M, N>(next, i, a, x, new_acc)
    } else {
        acc
    }
}

#[cap(a: shrd @ idx*N..M*N, x: shrd @ 0..N, y: uniq @ idx..M)]
fn mv_mul<const M: usize, const N: usize>(
    idx: usize,
    a: &[u32; { M * N }],
    x: &[u32; N],
    y: &mut [u32; M],
) {
    let cond = idx < M;
    if cond {
        let dot = cal_dot_product::<M, N>(0, idx, a, x, 0);
        y[idx] = dot;
        let one = 1;
        let next = idx + one;
        mv_mul::<M, N>(next, a, x, y)
    } else {
        ()
    }
}

#[cap(a: shrd @ 0..M*N, x: shrd @ 0..N, y: uniq @ 0..M)]
fn dmv<const M: usize, const N: usize>(a: &[u32; { M * N }], x: &[u32; N], y: &mut [u32; M]) {
    let start = 0;
    mv_mul::<M, N>(start, a, x, y)
}
