#[cap()]
pub fn sum(a: u32, b: u32, s: u32) -> u32 {
    let cond = a <= b;
    if cond {
        let new_s = s + a;
        let new_a = a + 1;
        sum(new_a, b, new_s)
    } else {
        s
    }
}
