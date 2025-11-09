#[cap(weight: shrd @ base..base+C, src: shrd @ j..C)]
fn row_dot<const RC: usize, const C: usize>(
    base: usize,
    j: usize,
    weight: &[i32; RC],
    src: &[i32; C],
    acc: i32,
) -> i32 {
    let done = j == C;
    if done {
        acc
    } else {
        let idx = base + j;
        let s_val = src[j];
        let w_val = weight[idx];
        let prod = s_val * w_val;
        let new_acc = acc + prod;
        let one = 1;
        let next = j + one;
        row_dot::<RC, C>(base, next, weight, src, new_acc)
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

#[cap(weight: shrd @ i..RC, src: shrd @ 0..C, dest: uniq @ i..R)]
fn rec_rows<const R: usize, const C: usize, const RC: usize>(
    i: usize,
    weight: &[i32; RC],
    src: &[i32; C],
    dest: &mut [i32; R],
    shift: usize,
) {
    let done = i == R;
    if done {
        ()
    } else {
        let base = i * C;
        let dot = row_dot::<RC, C>(base, 0, weight, src, 0);
        let shifted = dot >> shift;
        let clamped = clamp_i16(shifted);
        dest[i] = clamped;
        let one = 1;
        let next = i + one;
        rec_rows::<R, C, RC>(next, weight, src, dest, shift)
    }
}

#[cap(weight: shrd @ 0..RC, src: shrd @ 0..C, dest: uniq @ 0..R)]
fn nn_fc<const R: usize, const C: usize, const RC: usize>(
    weight: &[i32; RC],
    src: &[i32; C],
    dest: &mut [i32; R],
    shift: usize,
) {
    let start = 0;
    rec_rows::<R, C, RC>(start, weight, src, dest, shift)
}
