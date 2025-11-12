use dfx_macros::cap;

#[allow(unused_macros)]
macro_rules! fence {
    ($($tt:tt)*) => {};
}

#[cap]
fn sel1(cond: bool, a: i32, b: i32) -> i32 {
    if cond {
        a
    } else {
        b
    }
}

#[cap]
fn sel2(cond: bool, a: i32, b: i32) -> i32 {
    if cond {
        a
    } else {
        b
    }
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

        let err1 = out - max_pixel;
        let zero = 0;
        let dst_val = sel1(is_above, max_pixel, zero);
        let err_next = sel2(is_above, err1, out);
        dst[idx] = dst_val;
        fence!();
        dither_row_aux::<R, C>(next_j, i, err_next, src, dst)
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
