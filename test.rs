#[cap()]
pub fn simple(a: u32, b: u32) -> u32 {
    let c = a + b;
    let cond = c < 50;
    if cond {
        let r = c + 50;
        r
    } else {
        c
    }
}

// #[cap()]
// pub fn sum(a: u32, b: u32, s: u32) -> u32 {
//     let cond = a <= b;
//     if cond {
//         let new_s = s + a;
//         let new_a = a + 1;
//         sum(new_a, b, new_s)
//     } else {
//         s
//     }
// }
