use vstd::{prelude::*, seq};

verus! {

// fn foo() {
//     assert(1 == 0 + 1);
// }

struct Region<const N: usize>(Set<int>);

impl <const N: usize> Region<N> {
    // a region is well-formed if all its elements are in the range [0, N)
    spec fn wf(&self) -> bool {
        self.0.all(|i: int| 0 <= i < N as int)
        // self.0.subset_of(Set::new(|i: int| 0 <= i < N as int))
    }
}

fn par_load_shared<T: Copy, const N: usize>(i: usize, A: &[T; N], tracked A_cap: &Region<N>) -> (o: T) 
    // precondition: i ∈ A_cap (mimic sub-typing)
    requires 
            // A_cap.wf(), 
            A_cap.0 has (i as int),
            i < N,
    ensures
            o == A[i as int],
{
    A[i]
}

#[verifier(external_body)]
fn par_load_unique<T: Copy, const N: usize>(i: usize, A: &mut [T; N], Tracked(A_cap): Tracked<&mut Region<N>>) -> (o: T)
    requires
            // old(A_cap).wf(), 
            old(A_cap).0 has (i as int),
            i < N,
    // postcondition: A_cap' = A_cap \ {i} (mimic affine typing)
    ensures 
            // A_cap.wf(),
            A_cap.0 == old(A_cap).0.remove(i as int),
            o == A[i as int],
            *old(A) =~= *A,
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
            A[i as int] == t,
            forall |j| 0 <= j < N && j != i ==> A[j] == old(A)[j],
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

// breadth-first search based on CSR representation of graph
fn bfs<const R: usize, const V: usize, const E: usize>(
    rows: &[usize; R], // #Vertices + 1 = R
    cols: &[usize; E], // #Edges = E
    queue: &mut [usize; V], // queue capacity = V
    visited: &mut [usize; V],
    walk: &mut [usize; V],
    tracked rows_cap: &Region<R>,
    tracked cols_cap: &Region<E>,
    Tracked(queue_cap): Tracked<&mut Region<V>>,
    Tracked(visited_cap): Tracked<&mut Region<V>>,
    Tracked(walk_cap): Tracked<&mut Region<V>>,
)
    requires 
        V > 1,
        R == V + 1,
        forall |j| 0 <= j < R ==> rows[j] <= E,
        forall |j: int| 0 < j < R ==> rows[j - 1] <= #[trigger] rows[j] && rows[j] - rows[j - 1] <= V, // each vertex has at most V neighbors
        forall |j| 0 <= j < E ==> cols[j] < V,
        forall |i| 0 <= i < V ==> old(queue)[i] < V,
        // capacity constraints
        Set::new(|i: int| 0 <= i < R as int).subset_of(rows_cap.0),
        Set::new(|i: int| 0 <= i < E as int).subset_of(cols_cap.0),
        Set::new(|i: int| 0 <= i < V as int).subset_of(old(queue_cap).0),
        Set::new(|i: int| 0 <= i < V as int).subset_of(old(visited_cap).0),
        Set::new(|i: int| 0 <= i < V as int).subset_of(old(walk_cap).0),
{
    bfs_loop(rows, cols, queue, visited, walk, rows_cap, cols_cap, Tracked(queue_cap), Tracked(visited_cap), Tracked(walk_cap), 0, 1, 0);
}

fn bfs_loop<const R: usize, const V: usize, const E: usize>(
    rows: &[usize; R],
    cols: &[usize; E],
    queue: &mut [usize; V],
    visited: &mut [usize; V],
    walk: &mut [usize; V],
    tracked rows_cap: &Region<R>,
    tracked cols_cap: &Region<E>,
    Tracked(queue_cap): Tracked<&mut Region<V>>,
    Tracked(visited_cap): Tracked<&mut Region<V>>,
    Tracked(walk_cap): Tracked<&mut Region<V>>,
    qf: usize,
    qb: usize,
    wpos: usize,
)  
    requires
        V > 1,
        R == V + 1,
        qf <= qb < V,
        wpos == qf,
        forall |j| 0 <= j < R ==> rows[j] <= E,
        forall |j: int| 0 < j < R ==> rows[j - 1] <= #[trigger] rows[j] && rows[j] - rows[j - 1] <= V,
        forall |j| 0 <= j < E ==> cols[j] < V,
        forall |i| 0 <= i < V ==> old(queue)[i] < V,
        // capacity constraints
        Set::new(|i: int| 0 <= i < R as int).subset_of(rows_cap.0),
        Set::new(|i: int| 0 <= i < E as int).subset_of(cols_cap.0),
        Set::new(|i: int| qf <= i < V as int).subset_of(old(queue_cap).0),
        Set::new(|i: int| 0 <= i < V as int).subset_of(old(visited_cap).0),
        Set::new(|i: int| wpos <= i < V as int).subset_of(old(walk_cap).0),
    ensures
        forall |i| 0 <= i < V ==> queue[i] < V,
    decreases old(queue).len() - qf
{
    if qf == qb {
        ()
    } else { // qf < qb
        // dequeue front
        // let next = queue[qf];
        let next = par_load_unique(qf, queue, Tracked(queue_cap));
    
        // walk[wpos] = next;
        let _ = par_store(wpos, walk, next, Tracked(walk_cap));
    
        // neighbors: i in [rows[next], rows[next + 1])
        // let i0 = rows[next];
        // let iend = rows[next + 1];
        let i0 = par_load_shared(next, rows, rows_cap);
        let iend = par_load_shared(next + 1, rows, rows_cap);
    
        // enqueue unvisited neighbors; returns new queue_back
        let qb2 = enqueue_unvisited(cols, visited, queue, cols_cap, Tracked(visited_cap), Tracked(queue_cap), i0, iend, qb);
        
        fence::<V>(Tracked(queue_cap), Ghost(*old(queue_cap)));  // mimic fence here
        fence::<V>(Tracked(visited_cap), Ghost(*old(visited_cap)));  // mimic fence here
        bfs_loop(rows, cols, queue, visited, walk, rows_cap, cols_cap, Tracked(queue_cap), Tracked(visited_cap), Tracked(walk_cap), qf + 1, qb2, wpos + 1);
    }

}

fn enqueue_unvisited<const V: usize, const E: usize>(
    cols: &[usize; E],
    visited: &mut [usize; V],
    queue: &mut [usize; V],
    tracked cols_cap: &Region<E>,
    Tracked(visited_cap): Tracked<&mut Region<V>>,
    Tracked(queue_cap): Tracked<&mut Region<V>>,
    i: usize,
    iend: usize,
    qb: usize,
) -> (qb_2: usize) 
    requires
        V > 1,
        iend <= E,
        i <= iend && 0 <= iend - i <= V,
        qb < V,
        forall |j| 0 <= j < E ==> cols[j] < V,
        forall |j| 0 <= j < V ==> old(queue)[j] < V,
        // capacity constraints
        Set::new(|j: int| i <= j < iend as int).subset_of(cols_cap.0),
        Set::new(|j: int| 0 <= j < V as int).subset_of(old(visited_cap).0),
        Set::new(|j: int| qb <= j < V as int).subset_of(old(queue_cap).0),
    ensures
        qb <= qb_2 < V,
        forall |i| 0 <= i < V ==> queue[i] < V,
    decreases iend - i
{
    if i < iend {
        // let dst = cols[i];
        let dst = par_load_shared(i, cols, cols_cap);

        let is_visited = par_load_unique(dst, visited, Tracked(visited_cap));
        fence::<V>(Tracked(visited_cap), Ghost(*old(visited_cap)));  // mimic fence here
    
        // if visited[dst] == 0 {
        if is_visited == 0 {
            // visited[dst] = 1;
            // queue[qb] = dst;
            let _ = par_store(dst, visited, 1, Tracked(visited_cap));
            let _ = par_store(qb, queue, dst, Tracked(queue_cap));
            assume(qb + 1 < V); // need some ghost visited state to prove this
            fence::<V>(Tracked(visited_cap), Ghost(*old(visited_cap)));  // mimic fence here
            enqueue_unvisited(cols, visited, queue, cols_cap, Tracked(visited_cap), Tracked(queue_cap), i + 1, iend, qb + 1)
        } else {
            enqueue_unvisited(cols, visited, queue, cols_cap, Tracked(visited_cap), Tracked(queue_cap), i + 1, iend, qb)
        }
    } else {
        qb
    }

}



} // verus!
