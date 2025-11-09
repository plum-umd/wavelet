use vstd::prelude::*;

verus! {

// fn foo() {
//     assert(1 == 0 + 1);
// }

ghost struct Region<const N: usize>(Set<int>);

impl <const N: usize> Region<N> {
    // a region is well-formed if all its elements are in the range [0, N)
    spec fn wf(&self) -> bool {
        self.0.all(|i: int| 0 <= i < N as int)
        // self.0.subset_of(Set::new(|i: int| 0 <= i < N as int))
    }
}

fn par_load_shared<T: Copy, const N: usize>(i: usize, A: &[T; N], tracked A_cap: &Region<N>) -> T 
    // precondition: i ∈ A_cap (mimic sub-typing)
    requires 
            // A_cap.wf(), 
            A_cap.0 has (i as int),
            i < N,
{
    A[i]
}

#[verifier(external_body)]
fn par_load_unique<T: Copy, const N: usize>(i: usize, A: &mut [T; N], Tracked(A_cap): Tracked<&mut Region<N>>) -> (r: T)
    requires
            // old(A_cap).wf(), 
            old(A_cap).0 has (i as int),
            i < N,
    // postcondition: A_cap' = A_cap \ {i} (mimic affine typing)
    ensures 
            // A_cap.wf(),
            A_cap.0 == old(A_cap).0.remove(i as int),
{
    A[i]
}

#[verifier(external_body)]
fn par_store<T: Copy, const N: usize>(i: usize, A: &mut [T; N], t: T, Tracked(A_cap): Tracked<&mut Region<N>>) 
    requires
            // old(A_cap).wf(), 
            old(A_cap).0 has (i as int),
            i < N,
    ensures 
            // A_cap.wf(),
            A_cap.0 == old(A_cap).0.remove(i as int),
{
    A[i] = t;
}

#[verifier(external_body)]
fn fence<const N: usize>(Tracked(cap): Tracked<&mut Region<N>>, Ghost(old_cap): Ghost<Region<N>>)
    ensures cap.0 == old_cap.0
{
}

// a tail-recursive sum of an array A of length N, starting from index i, with accumulator a
fn sum<const N: usize>(i: usize, A: &[u32; N], tracked A_cap: &Region<N>, a: u32) -> u32 
    requires 
    // A_cap.wf(),
    // precondition: [i, N) ⊆ A_cap
    // mimic A: &{i..N} [u32; N]
    // requires Set::new(|j: int| i <= j < N as int) == A_cap.0,
        Set::new(|j: int| i <= j < N as int).subset_of(A_cap.0),
    decreases N - i,
{
    if i < N {
        let x = par_load_shared(i, A, A_cap);
        sum(i + 1, A, A_cap, a.wrapping_add(x))
    } else {
        a
    }
}

// a tail-recursive zeroing out an array from `i` to `N`:
fn zero_out<const N: usize>(i: usize, A: &mut [u32; N], Tracked(A_cap): Tracked<&mut Region<N>>) 
    // precondition: [i, N) ⊆ A_cap
    // mimic &uniq{i..N} [u32; N]
    requires Set::new(|j: int| i <= j < N as int).subset_of(old(A_cap).0)
    decreases N - i,
{
    if i < N {
        let _ = par_store(i, A, 0, Tracked(A_cap));
        zero_out(i + 1, A, Tracked(A_cap));
    } else {
        ()
    }
}

// copy array elements from array A to array B
fn copy_array<const N: usize>(i: usize, 
                            A: &[u32; N], 
                            B: &mut [u32; N], 
                            tracked A_cap: &Region<N>, 
                            Tracked(B_cap): Tracked<&mut Region<N>>) 
    // precondition: [i, N) ⊆ A_cap /\ [i, N) ⊆ B_cap
    // mimic A: &{i..N} [u32; N], B: &uniq{i..N} [u32; N]
    requires 
        Set::new(|j: int| i <= j < N as int).subset_of(A_cap.0),
        Set::new(|j: int| i <= j < N as int).subset_of(old(B_cap).0),
    decreases N - i,
{
    if i < N {
        let x = par_load_shared(i, A, A_cap);
        let _ = par_store(i, B, x, Tracked(B_cap));
        copy_array(i + 1, A, B, A_cap, Tracked(B_cap));
    } else {
        ()
    }
}

// add `1` to each element of array from `i` to `N`
fn increment<const N: usize>(i: usize, A: &mut [u32; N], Tracked(A_cap): Tracked<&mut Region<N>>) 
    // precondition: [i, N) ⊆ A_cap 
    // mimic &uniq{i..N} [u32; N]
    requires Set::new(|j: int| i <= j < N as int).subset_of(old(A_cap).0)
    decreases N - i,
{
    if i < N {
        let x = par_load_unique(i, A, Tracked(A_cap));
        fence::<N>(Tracked(A_cap), Ghost(*old(A_cap)));  // mimic fence here
        let x_add_1 = x.wrapping_add(1);
        let _ = par_store(i, A, x_add_1, Tracked(A_cap));
        increment(i + 1, A, Tracked(A_cap));
    } else {
        ()
    }
}

// Read-after-write
// for (j = 1; j < n; j++)
//   a[j] = a[j-1];
fn raw<const N: usize>(j: usize, A: &mut [u32; N], Tracked(A_cap): Tracked<&mut Region<N>>) 
    requires 
        j > 0,
        // mimic &uniq{j-1..N} [u32; N]
        Set::new(|i: int| j - 1 <= i < N as int).subset_of(old(A_cap).0),
    decreases N - j,
{
    if j < N {
        let x = par_load_unique(j - 1, A, Tracked(A_cap));
        let _ = par_store(j, A, x, Tracked(A_cap));
        fence::<N>(Tracked(A_cap), Ghost(*old(A_cap)));  // mimic fence here
        raw(j + 1, A, Tracked(A_cap));
    } else {
        ()
    }
}

// Write-after-read
// for (j = 0; j < n; j++)
//  a[j] = a[j + 1];
fn war<const N: usize>(j: usize, A: &mut [u32; N], Tracked(A_cap): Tracked<&mut Region<N>>) 
    requires 
        // mimic &uniq{j..N-1} [u32; N]
        Set::new(|i: int| j <= i < N as int).subset_of(old(A_cap).0),
    decreases N - j,
{
    if N > 1 {
        if j < N - 1 {
            let x = par_load_unique(j + 1, A, Tracked(A_cap));
            let _ = par_store(j, A, x, Tracked(A_cap));
            fence::<N>(Tracked(A_cap), Ghost(*old(A_cap)));  // mimic fence here
            war(j + 1, A, Tracked(A_cap));
        } else {
            ()
        }
    } else {
        ()
    }
}

// Write-after-write
// for (j = 0; j < n; j++) 
//   c[j] = j;  
//   c[j+1] = 5;
fn waw<const N: usize>(j: usize, C: &mut [usize; N], Tracked(C_cap): Tracked<&mut Region<N>>) 
    requires 
        // mimic &uniq{j..N-1} [u32; N]
        Set::new(|i: int| j <= i < N as int).subset_of(old(C_cap).0),
    decreases N - j,
{
    if N > 1 {
        if j < N - 1 {
            let _ = par_store(j, C, j, Tracked(C_cap));
            let _ = par_store(j + 1, C, 5, Tracked(C_cap));
            fence::<N>(Tracked(C_cap), Ghost(*old(C_cap)));  // mimic fence here
            waw(j + 1, C, Tracked(C_cap));
        } else {
            ()
        }
    } else {
        ()
    }
}

// matrix vector multiplication
fn mv_mul_const<const MN: usize, const M: usize, const N: usize>(idx: usize, 
                A: &[u32;  MN], 
                x: &[u32; N], 
                y: &mut [u32; M], 
                tracked A_cap: &Region<MN>, 
                tracked x_cap: &Region<N>, 
                Tracked(y_cap): Tracked<&mut Region<M>>) 
    // mimic A: &{0..N} [u32; MN], x: &{0..N} [u32; N], y: &uniq{idx..M} [u32; M]
    requires MN <= usize::MAX,
        MN == M * N,
        Set::new(|j: int| 0 <= j < M * N as int).subset_of(A_cap.0),
        Set::new(|j: int| 0 <= j < N as int).subset_of(x_cap.0),
        Set::new(|j: int| idx <= j < M as int).subset_of(old(y_cap).0),
    decreases M - idx,
{
    if idx < M {
        assert(Set::new(|k: int| idx * N <= k < (idx + 1) * N).subset_of(Set::new(|k: int| 0 <= k < M * N as int))) by (nonlinear_arith)
            requires
                idx < M,
                ;
        let dot_product = cal_dot_product_const::<MN, M, N>(0, idx, A, x, A_cap, x_cap, 0);
        let _ = par_store(idx, y, dot_product, Tracked(y_cap));
        mv_mul_const(idx + 1, A, x, y, A_cap, x_cap, Tracked(y_cap));
    } else {
        ()
    }
}

fn cal_dot_product_const<const MN: usize, const M: usize, const N: usize>(
    j: usize,
    i: usize,
    A: &[u32; MN],
    x: &[u32; N],
    tracked A_cap: &Region<MN>,
    tracked x_cap: &Region<N>,
    acc: u32,
) -> u32 
    requires MN <= usize::MAX, 
            MN == M * N,
            i < M,
            Set::new(|k: int| i * N <= k < (i + 1) * N).subset_of(A_cap.0),
            Set::new(|k: int| 0 <= k < N as int).subset_of(x_cap.0),
    decreases N - j,
{
    if j < N {
        assert(i * N  + j < MN) by (nonlinear_arith)
            requires
                MN <= usize::MAX,
                i < M,
                MN == M * N,
                j < N
                ;
        assert(A_cap.0 has (i * N + j)) by (nonlinear_arith)
            requires
                Set::new(|k: int| i * N <= k < (i + 1) * N as int).subset_of(A_cap.0),
                j < N
                ;
        let a_ij = par_load_shared(i * N + j, A, A_cap);
        let x_j = par_load_shared(j, x, x_cap);
        let acc = acc.wrapping_add(a_ij.wrapping_mul(x_j));
        cal_dot_product_const::<MN, M, N>(j + 1, i, A, x, A_cap, x_cap, acc)
    } else {
        acc
    }
}

fn mv_mul(idx: usize, 
                A: &[u32;  4], 
                x: &[u32; 2], 
                y: &mut [u32; 2], 
                tracked A_cap: &Region<4>, 
                tracked x_cap: &Region<2>, 
                Tracked(y_cap): Tracked<&mut Region<2>>) 
    // mimic A: &{0..4} [u32; 4], x: &{0..2} [u32; 2], y: &uniq{idx..2} [u32; 2]
    requires
        Set::new(|j: int| 0 <= j < 4 as int).subset_of(A_cap.0),
        Set::new(|j: int| 0 <= j < 2 as int).subset_of(x_cap.0),
        Set::new(|j: int| idx <= j < 2 as int).subset_of(old(y_cap).0),
    decreases 2 - idx,
{
    if idx < 2 {
        let dot_product = cal_dot_product(0, idx, A, x, A_cap, x_cap, 0);
        let _ = par_store(idx, y, dot_product, Tracked(y_cap));
        mv_mul(idx + 1, A, x, y, A_cap, x_cap, Tracked(y_cap));
    } else {
        ()
    }
}

fn cal_dot_product(
    j: usize,
    i: usize,
    A: &[u32; 4],
    x: &[u32; 2],
    tracked A_cap: &Region<4>,
    tracked x_cap: &Region<2>,
    acc: u32,
) -> u32 
    requires
            i < 2,
            Set::new(|k: int| i * 2 <= k < (i + 1) * 2).subset_of(A_cap.0),
            Set::new(|k: int| 0 <= k < 2 as int).subset_of(x_cap.0),
    decreases 2 - j,
{
    if j < 2 {
        let a_ij = par_load_shared(i * 2 + j, A, A_cap);
        let x_j = par_load_shared(j, x, x_cap);
        let acc = acc.wrapping_add(a_ij.wrapping_mul(x_j));
        cal_dot_product(j + 1, i, A, x, A_cap, x_cap, acc)
    } else {
        acc
    }
}




} // verus!
