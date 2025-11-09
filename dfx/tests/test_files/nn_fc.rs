#[cap(weight: shrd @ base..RC, src: shrd @ j..C)]
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
        let w_val = weight[idx];
        let s_val = src[j];
        let prod = s_val * w_val;
        let new_acc = acc + prod;
        let one = 1;
        let next = j + one;
        row_dot::<RC, C>(base, next, weight, src, new_acc)
    }
}

#[cap(weight: shrd @ i..RC, src: shrd @ 0..C, dest: uniq @ i..R)]
fn rec_rows<const R: usize, const C: usize, const RC: usize>(
    i: usize,
    weight: &[i32; RC],
    src: &[i32; C],
    dest: &mut [i32; R],
) {
    let done = i == R;
    if done {
        ()
    } else {
        let dot = row_dot::<RC, C>(i, 0, weight, src, 0);
        dest[i] = dot;
        let one = 1;
        let next = i + one;
        rec_rows::<R, C, RC>(next, weight, src, dest)
    }
}

#[cap(weight: shrd @ 0..RC, src: shrd @ 0..C, dest: uniq @ 0..R)]
fn nn_fc<const R: usize, const C: usize, const RC: usize>(
    weight: &[i32; RC],
    src: &[i32; C],
    dest: &mut [i32; R],
) {
    let start = 0;
    rec_rows::<R, C, RC>(start, weight, src, dest)
}
