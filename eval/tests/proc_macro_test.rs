// Test demonstrating compile-time type checking with dfx-macros

use dfx_macros::cap;

// Define the fence macro as a no-op for parsing
#[allow(unused_macros)]
macro_rules! fence {
    ($($tt:tt)*) => {};
}

#[cap(A: shrd @ i..N)]
fn sum<const N: usize>(i: usize, a: i32, A: &[i32; N]) -> i32 {
    let c = i < N;
    if c {
        let val = A[i];
        let one = 1;
        let j = i + one;
        let new_a = a + val;
        sum::<N>(j, new_a, A)
    } else {
        a
    }
}

#[cap(src: shrd @ i..N, dest: uniq @ i..N)]
fn copy_array<const N: usize>(i: usize, src: &[i32; N], dest: &mut [i32; N]) {
    let c = i < N;
    if c {
        let val = src[i];
        dest[i] = val;
        let one = 1;
        let j = i + one;
        copy_array::<N>(j, src, dest)
    } else {
        ()
    }
}

#[cap(A: uniq @ i..N)]
fn increment<const N: usize>(i: usize, A: &mut [usize; N]) {
    let c = i < N;
    if c {
        // p1: 0.5{i}, p2: 0.5{i}||1.0{i+1..N}
        let v = A[i];
        // p3, p_sync = join(p1, p2);
        let one = 1;
        let new_v = v + one;
        fence!();
        A[i] = new_v;
        let j = i + one;
        increment::<N>(j, A)
    } else {
        ()
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sum() {
        let arr = [1, 2, 3, 4, 5];
        let result = sum::<5>(0, 0, &arr);
        assert_eq!(result, 15);
    }

    #[test]
    fn test_copy() {
        let src = [1, 2, 3, 4, 5];
        let mut dest = [0; 5];
        copy_array::<5>(0, &src, &mut dest);
        assert_eq!(dest, src);
    }
}
