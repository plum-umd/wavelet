#[cap(res: uniq @ 0..1)]
pub fn sum_aux(a: u32, b: u32, res: &mut [u32; 1]) -> u32 {
    let cond = a <= b;
    if cond {
        let s = res[0];
        let new_s = s + a;
        fence!();
        res[0] = new_s;
        let new_a = a + 1;
        fence!();
        sum_aux(new_a, b, res)
    } else {
        let r = res[0];
        r
    }
}

#[cap(res: uniq @ 0..1)]
pub fn sum(a: u32, b: u32, #[alloc] res: &mut [u32; 1]) -> u32 {
    let z = 0u32;
    res[0] = z;
    fence!();
    sum_aux(a, b, res)
}
