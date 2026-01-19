#[cap(grid: uniq @ i-1..N)]
fn diffusion_step_aux<const N: usize>(i: usize, grid: &mut [i32; N]) {
    let one = 1;
    let ip1 = i + one;
    let cond1 = 0 < i;
    let cond2 = ip1 < N;
    let cond = cond1 && cond2;
    if cond {
        let prev = i - one;
        let next = i + one;
        let left = grid[prev];
        let center = grid[i];
        let right = grid[next];
        let sum_left_center = left + center;
        let total = sum_left_center + right;
        let avg = total / 3;
        fence!();
        grid[i] = avg;
        fence!();
        diffusion_step_aux::<N>(next, grid)
    } else {
        ()
    }
}

#[cap(grid: uniq @ 0..N)]
fn diffusion_step<const N: usize>(grid: &mut [i32; N]) {
    let start = 1;
    diffusion_step_aux::<N>(start, grid)
}