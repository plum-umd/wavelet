use dfx_macros::cap;

#[allow(unused_macros)]
macro_rules! fence {
    ($($tt:tt)*) => {};
}

#[cap(src: shrd @ i*C..i*C + C, dst: uniq @ i*C..i*C + C)]
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

        let pix = src[idx];
        let out = pix + err;

        let threshold = 256;
        let max_pixel = 0x1FF;
        let is_above = threshold < out;
        let one = 1;
        let next_j = j + one;
        fence!();

        if is_above {
            let err1 = out - max_pixel;
            dst[idx] = max_pixel;
            fence!();
            dither_row_aux::<R, C>(next_j, i, err1, src, dst)
        } else {
            let zero = 0;
            dst[idx] = zero;
            fence!();
            dither_row_aux::<R, C>(next_j, i, out, src, dst)
        }
    } else {
        ()
    }
}

#[cap(src: shrd @ i*C..R*C, dst: uniq @ i*C..R*C)]
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

#[cap(src: shrd @ 0..R*C, dst: uniq @ 0..R*C)]
pub fn dither<const R: usize, const C: usize>(src: &[i32; { R * C }], dst: &mut [i32; { R * C }]) {
    let start_i = 0;
    dither_aux::<R, C>(start_i, src, dst)
}
