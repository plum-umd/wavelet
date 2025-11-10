const SHRT_MIN: i32 = -32767;

fn pool_k_aux<const SRC: usize>(
    k: usize,
    pool_size: usize,
    src_offset: usize,
    j: usize,
    input_cols: usize,
    w: i32,
    src: &[i32; SRC],
) -> i32 {
    let cond = k < pool_size;
    if cond {
        let idx = src_offset + j * input_cols + k;
        let t = src[idx];
        let w1 = if t > w { t } else { w };

        let one = 1usize;
        let k1 = k + one;
        pool_k_aux::<SRC>(k1, pool_size, src_offset, j, input_cols, w1, src)
    } else {
        w
    }
}
fn pool_j_aux<const SRC: usize>(
    j: usize,
    pool_size: usize,
    src_offset: usize,
    input_cols: usize,
    w: i32,
    src: &[i32; SRC],
) -> i32 {
    let cond = j < pool_size;
    if cond {
        // Max across the k-loop for this row j
        let w_after_k = pool_k_aux::<SRC>(0, pool_size, src_offset, j, input_cols, w, src);

        let one = 1usize;
        let j1 = j + one;
        pool_j_aux::<SRC>(j1, pool_size, src_offset, input_cols, w_after_k, src)
    } else {
        w
    }
}

fn nn_pool_aux<const SRC: usize, const OUT: usize>(
    i: usize,
    src_offset: usize,
    col: usize,
    src: &[i32; SRC],
    dest: &mut [i32; OUT],
    input_rows_bump: usize,
    input_cols: usize,
    output_cols: usize,
    pool_size: usize,
) {
    let cond = i < OUT;
    if cond {
        // Inner two loops (j,k): compute max over pool_size x pool_size window
        let w0 = SHRT_MIN;
        let w = pool_j_aux::<SRC>(0, pool_size, src_offset, input_cols, w0, src);
        dest[i] = w;

        let one = 1usize;
        let i1 = i + one;

        let src_offset_right = src_offset + pool_size;
        let col1 = col + one;
        let end_of_row = col1 == output_cols;

        if end_of_row {
            let new_col = 0usize;
            let src_offset_next_row = src_offset_right + input_rows_bump;
            nn_pool_aux::<SRC, OUT>(
                i1,
                src_offset_next_row,
                new_col,
                src,
                dest,
                input_rows_bump,
                input_cols,
                output_cols,
                pool_size,
            )
        } else {
            nn_pool_aux::<SRC, OUT>(
                i1,
                src_offset_right,
                col1,
                src,
                dest,
                input_rows_bump,
                input_cols,
                output_cols,
                pool_size,
            )
        }
    } else {
        ()
    }
}

pub fn nn_pool<const SRC: usize, const OUT: usize>(
    src: &[i32; SRC],
    dest: &mut [i32; OUT],
    input_rows_bump: usize,
    input_cols: usize,
    output_cols: usize,
    pool_size: usize,
) {
    let start_i = 0usize;
    let start_off = 0usize;
    let start_col = 0usize;
    nn_pool_aux::<SRC, OUT>(
        start_i,
        start_off,
        start_col,
        src,
        dest,
        input_rows_bump,
        input_cols,
        output_cols,
        pool_size,
    )
}
