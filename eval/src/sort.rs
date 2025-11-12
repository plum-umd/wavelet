use dfx_macros::cap;

#[allow(unused_macros)]
macro_rules! fence {
    ($($tt:tt)*) => {};
}

#[cap(a: shrd @ j..j+1, z: shrd @ j..j+1)]
fn cond_read<const N: usize>(j: usize, odd: bool, a: &[i32; N], z: &[i32; N]) -> i32 {
    if odd {
        let ret = z[j];
        ret
    } else {
        let ret = a[j];
        ret
    }
}

#[cap(a: uniq @ j..j+1, z: uniq @ j..j+1)]
fn cond_write<const N: usize>(j: usize, odd: bool, a: &mut [i32; N], z: &mut [i32; N], v: i32) {
    if odd {
        a[j] = v;
    } else {
        z[j] = v;
    }
}

#[cap]
fn compute_next_count(zero_flag: bool, next_count: usize) -> usize {
    if zero_flag {
        let next_count2 = next_count + 1;
        next_count2
    } else {
        next_count
    }
}

#[cap]
fn sel1(cond: bool, a: usize, b: usize) -> usize {
    if cond { a } else { b }
}

#[cap]
fn sel2(cond: bool, a: usize, b: usize) -> usize {
    if cond { a } else { b }
}

#[cap]
fn sel3(cond: bool, a: usize, b: usize) -> usize {
    if cond { a } else { b }
}

#[cap(a: uniq @ 0..N, z: uniq @ 0..N)]
fn pass_aux<const N: usize>(
    j: usize,
    bit: usize,
    a: &mut [i32; N],
    z: &mut [i32; N],
    idx0: usize,
    idx1: usize,
    next_count: usize,
    odd: bool, // if true: src = Z, dst = A; else: src = A, dst = Z
) -> usize {
    let cond = j < N;
    if cond {
        // Read from the chosen source buffer
        let v = cond_read::<N>(j, odd, a, z);

        // Current bit and next higher bit check
        let v_shifted = v >> bit;
        let v_masked = v_shifted & 0x1;
        let zero = 0;
        let o = v_masked != zero;

        let bit_plus_one = bit + 1;
        let next_mask = 1i32 << bit_plus_one;

        let v_mask = v & next_mask;
        let mask_is_zero = v_mask == 0;
        let next_count2 = compute_next_count(mask_is_zero, next_count);
        let j1 = j + 1;
        fence!();

        let idx = sel1(o, idx1, idx0);
        let idx1b = idx1 + 1;
        let idx0b = idx0 + 1;

        let idx0n = sel2(o, idx0, idx0b);
        let idx1n = sel3(o, idx1b, idx1);

        // Write to the chosen destination buffer
        let safe = idx < N;
        if safe {
            cond_write::<N>(idx, odd, a, z, v);
            fence!();
            pass_aux::<N>(j1, bit, a, z, idx0n, idx1n, next_count2, odd)
        } else {
            next_count2
        }
    } else {
        next_count
    }
}

#[cap(a: uniq @ 0..N, z: uniq @ 0..N)]
fn sort_bits_aux<const N: usize>(bit: usize, count: usize, a: &mut [i32; N], z: &mut [i32; N]) {
    let cond = bit < 32;
    if cond {
        let zero = 0;
        let bit_mask = bit & 0x1;
        let odd = bit_mask != zero;

        let next_count = pass_aux::<N>(0, bit, a, z, 0, count, 0, odd);

        let bitp1 = bit + 1;
        fence!();
        sort_bits_aux::<N>(bitp1, next_count, a, z)
    } else {
        ()
    }
}

#[cap(a: uniq @ 0..N, z: uniq @ 0..N)]
pub fn sort<const N: usize>(a: &mut [i32; N], z: &mut [i32; N], even_count: usize) {
    sort_bits_aux::<N>(0, even_count, a, z)
}
