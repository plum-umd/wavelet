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
}

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
        let col_start = j;

        let w = dot_row_col_aux::<M, N, P>(0, row_base, col_start, a, b, 0);

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

pub fn dmm<const M: usize, const N: usize, const P: usize>(
    a: &[i32; { M * N }],
    b: &[i32; { N * P }],
    z: &mut [i32; { M * P }],
) {
    let start_i = 0;
    dmm_aux::<M, N, P>(start_i, a, b, z)
}
