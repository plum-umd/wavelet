use dfx_macros::cap;

// #[cap(a: shrd @ row_base..row_base + N, b: shrd @ 0..N*P)]
#[cap(a: shrd @ 0..M*N, b: shrd @ 0..N*P)]
fn dot_row_col_aux<const M: usize, const N: usize, const P: usize>(
    k: usize,
    row_base: usize,  // offset of A's row i: i * N
    col_start: usize, // offset of B's column j: j
    a: &[i32; { M * N }],
    b: &[i32; { N * P }],
    acc: i32,
) -> i32 {
    let cond = k < N;
    if cond {
        let idx_a = row_base + k;
        let kp = k * P;
        let idx_b = col_start + kp;
        let mn = M * N;
        let np = N * P;
        let safe1 = idx_a < mn;
        let safe2 = idx_b < np;
        let safe = safe1 && safe2;
        if safe {
            let a_val = a[idx_a];
            let b_val = b[idx_b];
            let prod = a_val * b_val;
            let new_acc = acc + prod;

            let one = 1;
            let next_k = k + one;
            dot_row_col_aux::<M, N, P>(next_k, row_base, col_start, a, b, new_acc)
        } else {
            acc
        }
    } else {
        acc
    }
}

// #[cap(a: shrd @ i*N..i*N + N, b: shrd @ 0..N*P, z: uniq @ i*P + j..i*P + P)]
#[cap(a: shrd @ 0..M*N, b: shrd @ 0..N*P, z: uniq @ i*P + j..i*P + P)]
#[inline(always)]
fn mm_row_aux<const M: usize, const N: usize, const P: usize>(
    j: usize,
    i: usize,
    a: &[i32; { M * N }],
    b: &[i32; { N * P }],
    z: &mut [i32; { M * P }],
) {
    let cond = j < P;
    if cond {
        let row_base = i * N;

        let w = dot_row_col_aux::<M, N, P>(0, row_base, j, a, b, 0);

        let ip = i * P;
        let dest_idx = ip + j;
        z[dest_idx] = w;

        let one = 1;
        let next_j = j + one;
        mm_row_aux::<M, N, P>(next_j, i, a, b, z)
    } else {
        ()
    }
}

// #[cap(a: shrd @ i*N..M*N, b: shrd @ 0..N*P, z: uniq @ i*P..M*P)]
#[cap(a: shrd @ 0..M*N, b: shrd @ 0..N*P, z: uniq @ i*P..M*P)]
fn dmm_aux<const M: usize, const N: usize, const P: usize>(
    i: usize,
    a: &[i32; { M * N }],
    b: &[i32; { N * P }],
    z: &mut [i32; { M * P }],
) {
    let cond = i < M;
    if cond {
        // Fill row i of Z
        let start_j = 0;
        mm_row_aux::<M, N, P>(start_j, i, a, b, z);

        let one = 1;
        let next_i = i + one;
        dmm_aux::<M, N, P>(next_i, a, b, z)
    } else {
        ()
    }
}

#[cap(a: shrd @ 0..M*N, b: shrd @ 0..N*P, z: uniq @ 0..M*P)]
pub fn dmm<const M: usize, const N: usize, const P: usize>(
    a: &[i32; { M * N }],
    b: &[i32; { N * P }],
    z: &mut [i32; { M * P }],
) {
    let start_i = 0;
    dmm_aux::<M, N, P>(start_i, a, b, z)
}
