#[cap(a: uniq @ i-1..N)]
fn prefix_sum_inplace_aux<const N: usize>(i: usize, a: &mut [i32; N]) {
    let one = 1;
    let cond_hi = i < N;
    let cond_lo = one <= i;
    let cont = cond_hi && cond_lo;
    if cont {
        let prev = i - one;
        let prev_val = a[prev];
        let curr = a[i];
        let new_val = curr + prev_val;
        fence!();
        a[i] = new_val; // a[i] = a[i] + a[i-1]
        fence!();
        let next = i + one;
        prefix_sum_inplace_aux::<N>(next, a)
    } else {
        ()
    }
}

#[cap(a: uniq @ 0..N)]
fn prefix_sum_inplace<const N: usize>(a: &mut [i32; N]) {
    let start = 1;
    prefix_sum_inplace_aux::<N>(start, a)
}
