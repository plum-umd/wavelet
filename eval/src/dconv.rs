use dfx_macros::cap;

// #[cap(a: shrd @ base..SRC, b: shrd @ 0..FROWS*FROWS)]
// #[cap(a: shrd @ 0..SRC, b: shrd @ 0..FROWS*FROWS)]
fn dconv_k_aux<const SRC: usize, const FROWS: usize, const FCOLS: usize>(
    k: usize,
    base: usize,  // row * SCOLS + col
    j: usize,     // 0..frows-1
    scols: usize, // source stride (columns)
    a: &[i32; SRC],
    b: &[i32; { FROWS * FROWS }], // matches C's B[j * frows + k]
    acc: i32,
) -> i32 {
    let cond = k < FCOLS;
    if cond {
        let scols_j = scols * j;
        let frows_j = j * FROWS;
        let a_offset = base + scols_j;
        let a_idx = a_offset + k;
        let b_idx = frows_j + k;
        let safe1 = a_idx < SRC;
        let frows_fcols = FROWS * FROWS;
        let a_val = a[a_idx];
        let b_val = b[b_idx];
        let prod = a_val * b_val;
        let new_acc = acc + prod;

        let one = 1usize;
        let k1 = k + one;
        dconv_k_aux::<SRC, FROWS, FCOLS>(k1, base, j, scols, a, b, new_acc)
    } else {
        acc
    }
}

// #[cap(a: shrd @ base..SRC, b: shrd @ 0..FROWS*FROWS)]
// #[cap(a: shrd @ 0..SRC, b: shrd @ 0..FROWS*FROWS)]
fn dconv_j_aux<const SRC: usize, const FROWS: usize, const FCOLS: usize>(
    j: usize,
    base: usize, // row * SCOLS + col
    scols: usize,
    a: &[i32; SRC],
    b: &[i32; { FROWS * FROWS }],
    acc: i32,
) -> i32 {
    let cond = j < FROWS;
    if cond {
        let acc_after_k = dconv_k_aux::<SRC, FROWS, FCOLS>(0, base, j, scols, a, b, acc);

        let one = 1usize;
        let j1 = j + one;
        dconv_j_aux::<SRC, FROWS, FCOLS>(j1, base, scols, a, b, acc_after_k)
    } else {
        acc
    }
}

// #[cap(a: shrd @ 0..SRC, b: shrd @ 0..FROWS*FROWS, z: uniq @ i..SIZE)]
fn dconv_i_aux<
    const SIZE: usize,
    const COLS: usize,
    const SCOLS: usize,
    const SRC: usize,
    const FROWS: usize,
    const FCOLS: usize,
>(
    i: usize,   // 0..SIZE-1
    row: usize, // current output row
    col: usize, // current output col
    a: &[i32; SRC],
    b: &[i32; { FROWS * FROWS }],
    z: &mut [i32; SIZE],
) {
    let cond = i < SIZE;
    if cond {
        // base offset = row * SCOLS + col
        let row_base = row * SCOLS;
        let base = row_base + col;

        // inner two loops over filter window
        let w = dconv_j_aux::<SRC, FROWS, FCOLS>(0, base, SCOLS, a, b, 0);
        z[i] = w;

        let one = 1usize;
        let col1 = col + one;
        let next_i = i + one;
        let end_row = col1 == COLS;
        if end_row {
            let next_row = row + one;
            let next_col = 0usize;
            dconv_i_aux::<SIZE, COLS, SCOLS, SRC, FROWS, FCOLS>(next_i, next_row, next_col, a, b, z)
        } else {
            dconv_i_aux::<SIZE, COLS, SCOLS, SRC, FROWS, FCOLS>(next_i, row, col1, a, b, z)
        }
    } else {
        ()
    }
}

// #[cap(a: shrd @ 0..SRC, b: shrd @ 0..FROWS*FROWS, z: uniq @ 0..SIZE)]
pub fn dconv<
    const SIZE: usize,
    const COLS: usize,
    const SCOLS: usize,
    const SRC: usize,
    const FROWS: usize,
    const FCOLS: usize,
>(
    a: &[i32; SRC],
    b: &[i32; { FROWS * FROWS }], // matches the C indexing j * frows + k
    z: &mut [i32; SIZE],
) {
    let start_i = 0usize;
    let start_row = 0usize;
    let start_col = 0usize;
    dconv_i_aux::<SIZE, COLS, SCOLS, SRC, FROWS, FCOLS>(start_i, start_row, start_col, a, b, z)
}
