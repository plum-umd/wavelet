const SHRT_MIN: i32 = -32767;
const SHRT_MAX: i32 = 32767;

fn dot_window_aux<const SRC: usize, const W: usize>(
    j: usize,
    row: usize,
    col: usize,
    src_idx: usize,
    base: usize,
    weight: &[i32; W],
    src: &[i32; SRC],
    weight_rows: usize,
    weight_cols: usize,
    wc_bump: usize,
    wc_wr_bump: usize,
    acc: i32,
) -> i32 {
    let cond = j < W;
    if cond {
        // accumulate
        let a = weight[j];
        let b = src[base + src_idx];
        let sum = acc + a * b;

        // advance scanning state
        let one = 1usize;
        let col1 = col + one;
        let src_idx1 = src_idx + one;

        let hit_col_end = col1 == weight_cols;
        if hit_col_end {
            let col2 = 0usize;
            let row1 = row + one;
            let src_idx2 = src_idx1 + wc_bump;

            let hit_row_end = row1 == weight_rows;
            if hit_row_end {
                let row2 = 0usize;
                let src_idx3 = src_idx2 + wc_wr_bump;
                let j1 = j + one;
                dot_window_aux::<SRC, W>(
                    j1,
                    row2,
                    col2,
                    src_idx3,
                    base,
                    weight,
                    src,
                    weight_rows,
                    weight_cols,
                    wc_bump,
                    wc_wr_bump,
                    sum,
                )
            } else {
                let j1 = j + one;
                dot_window_aux::<SRC, W>(
                    j1,
                    row1,
                    col2,
                    src_idx2,
                    base,
                    weight,
                    src,
                    weight_rows,
                    weight_cols,
                    wc_bump,
                    wc_wr_bump,
                    sum,
                )
            }
        } else {
            let j1 = j + one;
            dot_window_aux::<SRC, W>(
                j1,
                row,
                col1,
                src_idx1,
                base,
                weight,
                src,
                weight_rows,
                weight_cols,
                wc_bump,
                wc_wr_bump,
                sum,
            )
        }
    } else {
        acc
    }
}

fn nn_conv_aux<const SRC: usize, const W: usize, const OUT: usize>(
    i: usize,
    weight: &[i32; W],
    src: &[i32; SRC],
    dest: &mut [i32; OUT],
    weight_rows: usize,
    weight_cols: usize,
    wc_bump: usize,
    wc_wr_bump: usize,
    shift: u32,
) {
    let cond = i < OUT;
    if cond {
        // base offset for this output column
        let base = i;

        // compute convolution dot-product over the current window
        let w_raw = dot_window_aux::<SRC, W>(
            0,
            0,
            0,
            0,
            base,
            weight,
            src,
            weight_rows,
            weight_cols,
            wc_bump,
            wc_wr_bump,
            0,
        );

        // shift and clamp to [SHRT_MIN, SHRT_MAX]
        let shifted = w_raw >> shift;
        let clipped_low = if shifted < SHRT_MIN {
            SHRT_MIN
        } else {
            shifted
        };
        let clipped_high = if clipped_low > SHRT_MAX {
            SHRT_MAX
        } else {
            clipped_low
        };

        dest[i] = clipped_high;

        // next output position
        let one = 1usize;
        let j = i + one;
        nn_conv_aux::<SRC, W, OUT>(
            j,
            weight,
            src,
            dest,
            weight_rows,
            weight_cols,
            wc_bump,
            wc_wr_bump,
            shift,
        )
    } else {
        ()
    }
}

pub fn nn_conv<const SRC: usize, const W: usize, const OUT: usize>(
    weight: &[i32; W],
    src: &[i32; SRC],
    dest: &mut [i32; OUT],
    weight_rows: usize,
    weight_cols: usize,
    wc_bump: usize,
    wc_wr_bump: usize,
    shift: u32,
) {
    let start = 0usize;
    nn_conv_aux::<SRC, W, OUT>(
        start,
        weight,
        src,
        dest,
        weight_rows,
        weight_cols,
        wc_bump,
        wc_wr_bump,
        shift,
    )
}
