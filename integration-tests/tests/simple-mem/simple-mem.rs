#[cap(res: uniq @ 0..1)]
pub fn sum(a: u32, b: u32, res: &mut [u32; 1]) {
    let cond = a <= b;
    if cond {
        let s = res[0];
        let new_s = s + a;
        fence!();
        res[0] = new_s;
        let new_a = a + 1;
        fence!();
        sum(new_a, b, res)
    } else {
        ()
    }
}
