#[cap(weight: shrd @ i*C..i*C + C, src: shrd @ j..C)]
fn row_dot<const R: usize, const C: usize>(
    i: usize,
    j: usize,
    weight: &[i32; { R * C }],
    src: &[i32; C],
    acc: i32,
) -> i32 {
    let cond = j < C;
    if cond {
        let base = i * C;
        let idx = base + j;
        let s_val = src[j];
        let w_val = weight[idx];
        let prod = s_val * w_val;
        let new_acc = acc + prod;
        let one = 1;
        let next = j + one;
        row_dot::<R, C>(i, next, weight, src, new_acc)
    } else {
        acc
    }
}

fn clamp_i16(w: i32) -> i32 {
    let min = -32768;
    let below = w < min;
    if below {
        min
    } else {
        let max = 32767;
        let above = max < w;
        if above {
            max
        } else {
            w
        }
    }
}

#[cap(weight: shrd @ i*C..R*C, src: shrd @ 0..C, dest: uniq @ i..R)]
fn rec_rows<const R: usize, const C: usize>(
    i: usize,
    weight: &[i32; { R * C }],
    src: &[i32; C],
    dest: &mut [i32; R],
    shift: usize,
) {
    let cond = i < R;
    if cond {
        let dot = row_dot::<R, C>(i, 0, weight, src, 0);
        let shifted = dot >> shift;
        let clamped = clamp_i16(shifted);
        dest[i] = clamped;
        let one = 1;
        let next = i + one;
        rec_rows::<R, C>(next, weight, src, dest, shift)
    } else {
        ()
    }
}

#[cap(weight: shrd @ 0..R*C, src: shrd @ 0..C, dest: uniq @ 0..R)]
fn nn_fc<const R: usize, const C: usize>(
    weight: &[i32; { R * C }],
    src: &[i32; C],
    dest: &mut [i32; R],
    shift: usize,
) {
    let start = 0;
    rec_rows::<R, C>(start, weight, src, dest, shift)
}
