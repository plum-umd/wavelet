fn dot_patch_aux<const SRC: usize, const FROWS: usize, const FCOLS: usize>(
    t: usize,
    limit: usize, // FROWS * FCOLS
    base: usize,  // row * SCOLS + col
    scols: usize, // source stride (columns)
    a: &[i32; SRC],
    b: &[i32; { FROWS * FROWS }], // note: matches the C indexing j * frows + k
    acc: i32,
) -> i32 {
    let cond = t < limit;
    if cond {
        let j = t / FCOLS;
        let k = t % FCOLS;

        let a_idx = base + j * scols + k;
        let b_idx = j * FROWS + k; // faithful to the provided C code

        let prod = a[a_idx] * b[b_idx];
        let new_acc = acc + prod;

        let one = 1usize;
        let next = t + one;
        dot_patch_aux::<SRC, FROWS, FCOLS>(next, limit, base, scols, a, b, new_acc)
    } else {
        acc
    }
}

fn dconv_aux<
    const SIZE: usize,
    const COLS: usize,
    const SCOLS: usize,
    const SRC: usize,
    const FROWS: usize,
    const FCOLS: usize,
>(
    i: usize,
    row: usize,
    col: usize,
    a: &[i32; SRC],
    b: &[i32; { FROWS * FROWS }],
    z: &mut [i32; SIZE],
) {
    let cond = i < SIZE;
    if cond {
        let base = row * SCOLS + col;
        let limit = FROWS * FCOLS;
        let w = dot_patch_aux::<SRC, FROWS, FCOLS>(0, limit, base, SCOLS, a, b, 0);

        z[i] = w;

        // advance over the output image in row-major order
        let one = 1usize;
        let col1 = col + one;
        let end_row = col1 == COLS;

        if end_row {
            let next_row = row + one;
            let next_col = 0usize;
            let next_i = i + one;
            dconv_aux::<SIZE, COLS, SCOLS, SRC, FROWS, FCOLS>(next_i, next_row, next_col, a, b, z)
        } else {
            let next_i = i + one;
            dconv_aux::<SIZE, COLS, SCOLS, SRC, FROWS, FCOLS>(next_i, row, col1, a, b, z)
        }
    } else {
        ()
    }
}

pub fn dconv<
    const SIZE: usize,
    const COLS: usize,
    const SCOLS: usize,
    const SRC: usize,
    const FROWS: usize,
    const FCOLS: usize,
>(
    a: &[i32; SRC],
    b: &[i32; { FROWS * FROWS }], // matches C's B[j * frows + k] indexing
    z: &mut [i32; SIZE],
) {
    let start_i = 0usize;
    let start_row = 0usize;
    let start_col = 0usize;
    dconv_aux::<SIZE, COLS, SCOLS, SRC, FROWS, FCOLS>(start_i, start_row, start_col, a, b, z)
}
