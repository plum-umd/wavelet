fn cond_read<const N: usize>(j: usize, odd: bool, a: &[i32; N], z: &[i32; N]) -> i32 {
    if odd { z[j] } else { a[j] }
}

fn cond_write<const N: usize>(j: usize, odd: bool, a: &mut [i32; N], z: &mut [i32; N], v: i32) {
    if odd {
        a[j] = v;
    } else {
        z[j] = v;
    }
}

fn pass_aux<const N: usize>(
    j: usize,
    bit: usize,
    size: usize,
    a: &mut [i32; N],
    z: &mut [i32; N],
    idx0: usize,
    idx1: usize,
    next_count: usize,
    odd: bool, // if true: src = Z, dst = A; else: src = A, dst = Z
) -> usize {
    let cond = j < size;
    if cond {
        // Read from the chosen source buffer
        let v = cond_read::<N>(j, odd, a, z);

        // Current bit and next higher bit check
        let o = ((v >> (bit as u32)) & 0x1) != 0;
        let next_mask = 1i32 << ((bit + 1) as u32);
        let next_count2 = next_count + ((v & next_mask) == 0) as usize;
        let j1 = j + 1;

        // Write to the chosen destination buffer
        if o {
            cond_write::<N>(idx1, odd, a, z, v);
            let idx1b = idx1 + 1;
            pass_aux::<N>(j1, bit, size, a, z, idx0, idx1b, next_count2, odd)
        } else {
            cond_write::<N>(idx0, odd, a, z, v);
            let idx0b = idx0 + 1;
            pass_aux::<N>(j1, bit, size, a, z, idx0b, idx1, next_count2, odd)
        }
    } else {
        next_count
    }
}

fn sort_bits_aux<const N: usize>(
    bit: usize,
    count: usize,
    size: usize,
    a: &mut [i32; N],
    z: &mut [i32; N],
) {
    let cond = bit < 32;
    if cond {
        let odd = (bit & 0x1) != 0;

        let next_count = pass_aux::<N>(0, bit, size, a, z, 0, count, 0, odd);

        sort_bits_aux::<N>(bit + 1, next_count, size, a, z)
    } else {
        ()
    }
}

pub fn sort<const N: usize>(a: &mut [i32; N], z: &mut [i32; N], size: usize, even_count: usize) {
    sort_bits_aux::<N>(0, even_count, size, a, z)
}
