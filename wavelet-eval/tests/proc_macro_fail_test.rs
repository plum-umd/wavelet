// Test that demonstrates compile-time error detection

use dfx_macros::cap;

// This should fail type checking - accessing beyond the declared capability
#[cap(arr: shrd @ i..N)]
fn bad_access<const N: usize>(i: usize, arr: &[i32; N]) -> i32 {
    let c = i < N;
    if c {
        // This access at index 0 is outside the declared capability i..N
        let val = arr[0];  // Should cause compile error
        val
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bad() {
        let arr = [1, 2, 3, 4, 5];
        let _ = bad_access::<5>(2, &arr);
    }
}
