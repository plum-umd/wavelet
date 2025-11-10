fn dither_row_aux<const R: usize, const C: usize>(
    j: usize,
    i: usize,
    err: i32,
    src: &[i32; { R * C }],
    dst: &mut [i32; { R * C }],
) {
    let cond = j < C;
    if cond {
        let idx_mul = i * C;
        let idx = idx_mul + j;

        let out = src[idx] + err;

        let threshold = 256;
        let max_pixel = 0x1FF;
        let is_above = out > threshold;
        let one = 1;
        let next_j = j + one;

        if is_above {
            let pixel = max_pixel;
            let new_err = out - pixel;
            dst[idx] = pixel;
            dither_row_aux::<R, C>(next_j, i, new_err, src, dst)
        } else {
            let pixel = 0;
            let new_err = out;
            dst[idx] = pixel;
            dither_row_aux::<R, C>(next_j, i, new_err, src, dst)
        }
    } else {
        ()
    }
}

fn dither_aux<const R: usize, const C: usize>(
    i: usize,
    src: &[i32; { R * C }],
    dst: &mut [i32; { R * C }],
) {
    let cond = i < R;
    if cond {
        // per-row error accumulator starts at 0
        let start_err = 0;
        let start_j = 0;
        dither_row_aux::<R, C>(start_j, i, start_err, src, dst);

        let one = 1;
        let next_i = i + one;
        dither_aux::<R, C>(next_i, src, dst)
    } else {
        ()
    }
}

pub fn dither<const R: usize, const C: usize>(src: &[i32; { R * C }], dst: &mut [i32; { R * C }]) {
    let start_i = 0;
    dither_aux::<R, C>(start_i, src, dst)
}
