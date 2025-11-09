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

fn par_load_shared<T: Copy, const N: usize>(i: u32, A: &[T; N], tracked A_cap: &Region<N>) -> T 
    // precondition: i ∈ A_cap (mimic sub-typing)
    requires 
            // A_cap.wf(), 
            A_cap.0 has (i as int),
            i < N,
{
    A[i as usize]
}

#[verifier(external_body)]
fn par_load_unique<T: Copy, const N: usize>(i: u32, A: &mut [T; N], Tracked(A_cap): Tracked<&mut Region<N>>) -> (r: T)
    requires 
            // old(A_cap).wf(), 
            old(A_cap).0 has (i as int),
            i < N,
    // postcondition: A_cap' = A_cap \ {i} (mimic affine typing)
    ensures 
            // A_cap.wf(),
            A_cap.0 == old(A_cap).0.remove(i as int),
{
    A[i as usize]
}

#[verifier(external_body)]
fn par_store<T: Copy, const N: usize>(i: u32, A: &mut [T; N], t: T, Tracked(A_cap): Tracked<&mut Region<N>>) 
    requires
            // old(A_cap).wf(), 
            old(A_cap).0 has (i as int),
            i < N,
    ensures 
            // A_cap.wf(),
            A_cap.0 == old(A_cap).0.remove(i as int),
{
    A[i as usize] = t;
}

// a tail-recursive sum of an array A of length N, starting from index i, with accumulator a
fn sum<const N: usize>(i: u32, A: &[u32; N], tracked A_cap: &Region<N>, a: u32) -> u32 
    requires 
    // A_cap.wf(),
    // precondition: [i, N) ⊆ A_cap
    // mimic A: &{i..N} [u32; N]
    // requires Set::new(|j: int| i <= j < N as int) == A_cap.0,
        Set::new(|j: int| i <= j < N as int).subset_of(A_cap.0),
    decreases N - i,
{
    if i < N as u32 {
        let x = par_load_shared(i, A, A_cap);
        sum(i + 1, A, A_cap, a.wrapping_add(x))
    } else {
        a
    }
}

// a tail-recursive zeroing out an array from `i` to `N`:
fn zero_out<const N: usize>(i: u32, A: &mut [u32; N], Tracked(A_cap): Tracked<&mut Region<N>>) 
    // precondition: [i, N) ⊆ A_cap
    // mimic &uniq{i..N} [u32; N]
    requires Set::new(|j: int| i <= j < N as int).subset_of(old(A_cap).0)
    decreases N - i,
{
    if i < N as u32 {
        let _ = par_store(i, A, 0, Tracked(A_cap));
        zero_out(i + 1, A, Tracked(A_cap));
    } else {
        ()
    }
}

// copy array elements from array A to array B
fn copy_array<const N: usize>(i: u32, 
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
    if i < N as u32 {
        let x = par_load_shared(i, A, A_cap);
        let _ = par_store(i, B, x, Tracked(B_cap));
        copy_array(i + 1, A, B, A_cap, Tracked(B_cap));
    } else {
        ()
    }
}

// add `1` to each element of array from `i` to `N`
fn increment<const N: usize>(i: u32, A: &mut [u32; N], Tracked(A_cap): Tracked<&mut Region<N>>) 
    // precondition: [i, N) ⊆ A_cap 
    // mimic &uniq{i..N} [u32; N]
    requires Set::new(|j: int| i <= j < N as int).subset_of(old(A_cap).0)
    decreases N - i,
{
    if i < N as u32 {
        // let x = par_load_unique(i, A, Tracked(A_cap));
        let x = A[i as usize]; // mimic fence here
        // ---
        let x_add_1 = x.wrapping_add(1);
        let _ = par_store(i, A, x_add_1, Tracked(A_cap));
        // A[i as usize] = x_add_1; // mimic fence here
        increment(i + 1, A, Tracked(A_cap));
    } else {
        ()
    }
}

// Read-after-write
// for (j = 1; j < n; j++)
//   a[j] = a[j-1];
fn raw<const N: usize>(j: u32, A: &mut [u32; N], Tracked(A_cap): Tracked<&mut Region<N>>) 
    requires 
        j > 0,
        // mimic &uniq{j-1..N} [u32; N]
        Set::new(|i: int| j - 1 <= i < N as int).subset_of(old(A_cap).0),
    decreases N - j,
{
    if j < N as u32 {
        let x = par_load_unique(j - 1, A, Tracked(A_cap));
        // let _ = par_store(j, A, x, Tracked(A_cap));
        A[j as usize] = x; // mimic fence here
        // ---
        raw(j + 1, A, Tracked(A_cap));
    } else {
        ()
    }
}

// Write-after-read
// for (j = 0; j < n; j++)
//  a[j] = a[j + 1];
fn war<const N: usize>(j: u32, A: &mut [u32; N], Tracked(A_cap): Tracked<&mut Region<N>>) 
    requires 
        // mimic &uniq{j..N-1} [u32; N]
        Set::new(|i: int| j <= i < N as int).subset_of(old(A_cap).0),
    decreases N - j,
{
    if j < N as u32 - 1 {
        let x = par_load_unique(j + 1, A, Tracked(A_cap));
        let _ = par_store(j, A, x, Tracked(A_cap));
        war(j + 1, A, Tracked(A_cap));
    } else {
        ()
    }
}

} // verus!
