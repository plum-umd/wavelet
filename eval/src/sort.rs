fn pass_aux<const N: usize>(
    j: usize,
    bit: usize,
    src: &[i32; N],
    dst: &mut [i32; N],
    idx0: usize,
    idx1: usize,
    next_count: usize,
) -> usize {
    let cond = j < N;
    if cond {
        let v = src[j];
        // Current bit
        let o = ((v >> (bit as u32)) & 0x1) != 0;
        // Count how many have next higher bit == 0
        let mask_next = 1i32 << ((bit + 1) as u32);
        let next_count2 = next_count + ((v & mask_next) == 0) as usize;

        if o {
            dst[idx1] = v;
            let one = 1;
            let j1 = j + one;
            let idx1b = idx1 + one;
            pass_aux::<N>(j1, bit, src, dst, idx0, idx1b, next_count2)
        } else {
            dst[idx0] = v;
            let one = 1;
            let j1 = j + one;
            let idx0b = idx0 + one;
            pass_aux::<N>(j1, bit, src, dst, idx0b, idx1, next_count2)
        }
    } else {
        next_count
    }
}

fn sort_bits_aux<const N: usize>(bit: usize, count: usize, a: &mut [i32; N], z: &mut [i32; N]) {
    let cond = bit < 32;
    if cond {
        // Alternate src/dst each bit (even: A->Z, odd: Z->A)
        let odd = (bit & 0x1) != 0;
        if odd {
            // src = Z (imm), dst = A (mut)
            let src: &[i32; N] = &*z;
            let dst: &mut [i32; N] = &mut *a;
            let next_count = pass_aux::<N>(0, bit, src, dst, 0, count, 0);
            let one = 1;
            sort_bits_aux::<N>(bit + one, next_count, a, z)
        } else {
            // src = A (imm), dst = Z (mut)
            let src: &[i32; N] = &*a;
            let dst: &mut [i32; N] = &mut *z;
            let next_count = pass_aux::<N>(0, bit, src, dst, 0, count, 0);
            let one = 1;
            sort_bits_aux::<N>(bit + one, next_count, a, z)
        }
    } else {
        // After 32 passes, the result ends up in A (since the last pass is odd).
        // If the last pass wrote into Z (when bit 31 is odd, it wrote into A), we’re already done.
        ()
    }
}

pub fn sort<const N: usize>(a: &mut [i32; N], z: &mut [i32; N], even_count: usize) {
    // even_count initializes the split point (idx1) for the first pass
    sort_bits_aux::<N>(0, even_count, a, z)
}
