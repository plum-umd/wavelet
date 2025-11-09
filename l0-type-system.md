# Type system for L0

## RipTide example C programs

```c
void for_if_for(
    const uint16_t * restrict A, 
    const uint16_t * restrict B, 
    uint16_t * restrict C, 
    uint16_t * restrict D, 
    uint16_t * restrict Z, 
    uint16_t lenC,
    uint16_t lenD
)
{
    for (uint16_t i = 0 ; i < lenC ; i++) {
        if (A[i] < B[i]) {
            for (uint16_t j = 0 ; j < lenD ; j++) {
                Z[i] += D[j] * 2;
            }
        }
    }

    return;
}

void for_if_for_else(
    const uint16_t * restrict A, 
    const uint16_t * restrict B, 
    uint16_t * restrict C, 
    uint16_t * restrict D, 
    uint16_t * restrict Z, 
    uint16_t lenC,
    uint16_t lenD
)
{
    for (uint16_t i = 0 ; i < lenC ; i++) {
        if (A[i] < B[i]) {
            for (uint16_t j = 0 ; j < lenD ; j++) {
                Z[i] += D[j] * 2;
            }
        } else {
            Z[i] = A[i] * 4;
        }
        Z[i] += 20;
    }

    return;
}

void for_if_then_else(
    const uint16_t * restrict A, 
    const uint16_t * restrict B, 
    uint16_t * restrict C, 
    uint16_t * restrict D, 
    uint16_t * restrict Z, 
    uint16_t lenC,
    uint16_t lenD
)
{
    for (uint16_t i = 0 ; i < lenC ; i++) {
        uint16_t a = 0;
        if (A[i] < B[i]) {
            a = D[i] * 2;
        }
        else {
            a = Z[i]; 
        }
        Z[i] += a;
    }

    return;
}

void if_for(uint16_t * restrict A, uint16_t * restrict B, uint16_t * restrict C, uint16_t * restrict Z, uint16_t len)
{
    if (*A < *B)
    {
        for (uint16_t i = 0 ; i < len ; i++) {
            Z[i] = C[i] * 2; 
        }
    }
    return;
}

void for_if_else_if_else_short(
    const uint16_t * restrict A, 
    const uint16_t * restrict B, 
    uint16_t * restrict C, 
    uint16_t * restrict D, 
    uint16_t * restrict Z, 
    uint16_t lenC,
    uint16_t lenD
)
{
    uint16_t a = 0;
    for (uint16_t i = 0 ; i < lenC ; i++) {
        a += Z[i];
        if (A[i] < (B[i] + a)) {
            //
        } 
        else {
            Z[i] = 0;
        }
        Z[i] += 20 + a;
    }

    return;
}

void for_if_else_if_else_write(
    const uint16_t * restrict A, 
    const uint16_t * restrict B, 
    uint16_t * restrict C, 
    uint16_t * restrict D, 
    uint16_t * restrict Z, 
    uint16_t lenC,
    uint16_t lenD
)
{
    uint16_t a = 0;
    for (uint16_t i = 0 ; i < lenC ; i++) {
        // a += Z[i];
        if (A[i] < B[i]) {
            Z[i] = D[i] * 2;
            // D[i] = 0;
            // a += Z[i];
        } 
        else if (A[i] == B[i]) {
            Z[i] += C[i];
            // a += Z[i];
            // a += 2;
        }
        else {
            // a += Z[i];
            Z[i] = 0;
        }
        Z[i] += 20; // + a;
    }

    // C[0] = a;

    return;
}

#if 0
void dmm(CONST_PTR(int16_t) A, CONST_PTR(int16_t) B, PTR(int16_t) Z, 
	uint32_t m, uint32_t n, uint32_t p) {
	for(uint32_t i = 0; i < m; i++) {
		for(uint32_t j = 0; j < p; j++) {
			int16_t w = 0;
			for(uint32_t k = 0; k < n; k++) {
				w += clip(A[i * n + k] * B[k * p + j], 5);
			}
			Z[i * p + j] = w;
		}
	}
}
#else
void dmm(CONST_PTR(int16_t) A, CONST_PTR(int16_t) B, PTR(int16_t) Z, 
	uint32_t m, uint32_t n, uint32_t p) {
	
	uint32_t dest_idx = 0;	
	CONST_PTR(int16_t) filter_ptr = A;
	for(uint32_t i = 0; i < m; i++) {
		for(uint32_t j = 0; j < p; j++) {
			int16_t w = 0;
			uint32_t src_idx = j;
			for(uint32_t k = 0; k < n; k++) {
				w += filter_ptr[k] * B[src_idx];
				src_idx += p;
			}
			Z[dest_idx++] = w;
		}
		filter_ptr += n;
	}
}
#endif

void dmv(CONST_PTR(int16_t) A, CONST_PTR(int16_t) B, 
	PTR(int16_t) Z, uint32_t m, uint32_t n) {
	for(uint32_t i = 0; i < m; i++) {
		int16_t w = 0;
		for(uint32_t j = 0; j < n; j++) {
			w += A[i * n + j] * B[j];
		}
		Z[i] = w;
	}
}

```

## Problem Description

We want our L0 → L1 compiler to maximize parallelism (preferably enable all possible pipelining) but keep necessary memory ordering (keep original semantics and avoid data races). Based on the prior discussion, a *fine-grained permission system* on top of L0 looks promising for enforcing memory ordering. For pipelining though, this amounts to figure out all potential memory dependencies present *across loop iterations*.

It turns out there is a whole bunch of research/techniques for loop dependence analysis: [https://en.wikipedia.org/wiki/Loop_dependence_analysis](https://en.wikipedia.org/wiki/Loop_dependence_analysis).

RipTide compiler, being an unverified compiler, seemed to be quite conservative and not apply such analysis aggressively. The questions now becomes: 

1. can our type/permission system “subsume” those loop dependence analysis and hence allows us to provably omit ordering edges?
2. if the answer to 1. is yes, how automated this process can be?
3. if the answer to 2. is “it depends”, what patterns can be fully-automated and what cannot?

### Memory dependence analysis: the intuition

Given two memory ops accessing *the same region* (for the sake of simplicity, we only consider `load`/`store` by array indexing), if *at least one* of them is a `store`, we must serialize the two ops (either two different ops in the same loop iteration, or two instances of those two ops across different iterations).

**Classical Examples**

read-after-write (RAW)

```c
for (j = 1; j < n; j++)
    S1: a[j] = a[j-1];
```

 write-after-read (WAR)

```c
for (j = 0; j < n; j++)
    S1: b[j] = b[j+1];
```

write-after-write (WAW)

```c
for (j = 0; j < n; j++) {
    S1: c[j] = j;  
    S2: c[j+1] = 5;
}
```

Loop-carried dependencies present in above programs are pretty easy to see, but there’re programs that need more fine grained dependence analysis to be (not) pipelined:

```c
// can be pipelined
for (i=0; i < 100; i++) {
  S1: a[2*i] = ...
  S2: ... = a[4*i + 1]
}

// cannot be pipelined
for (i=0; i < 100; i++) {
  S1: a[2*i] = ...
  S2: ... = a[2*i + 4]
}
```

Most RipTide example C programs above do *not* have any loop-carried dependence

- statements like `Z[i] += 20;` (a `load` followed by a `store`) have *loop independent* dependence

### Typing L0 programs: the intuition (v.0)

Sum elements of an array from `i` to `N`:

```rust
// `A: &{i..N} [u32; N]` represents read-only (shared) permission for `A` from `i` to `N`
fn sum<const N: usize>(i: u32, A: &{i..N} [u32; N], a: u32) -> u32 =
  let c = i < N;
  if c {
    let val = load(i, A);  // `load(i, A)` needs `A: &{i} [T; N] where i < N` (shared permission)
												   // `A: &{i..N} [u32; N]` (doesn't change as `&{i..N} [u32; N] \ &{i} [T; N]` remains `&{i..N} [T; N]`)
    sum(i + 1, A, val + a) // sub-typing gives `&{i..N} [u32; N] <: &{i+1..N} [u32; N]`
  } else {
    a
  }
```

Zero out an array from `i` to `N`:

```rust
// `f` needs a _unique_ and _spatial_ permission of `i..N` for the arrary A
fn f<const N: usize>(i: u32, A: &uniq{i..N} [u32; N]) =
  let c = i < N;
  if c {
    let _ = store(i, A, 0); // `store(i, A, x)` needs `A: &uniq{i} [T; N] where i < N`
                            // `A: &uniq{i+1..N} [u32; N]` (lose permission at `i`)
    f(i + 1, A) // recursive call tycks and pipelining enabled!
  } else {
    ()
  }
```

Copy array elements from array A to array B (explicit data dependency):

```rust
// type system tells us that `A` and `B` won't alias
fn copy_array<const N: usize>(i: u32, 
															A: &{i..N} [u32; N], 
															B: &uniq{i..N} [u32; N]) =
  let c = i < N;
  if c {
    let val = load(i, A); // `load(i, A)` needs `A: &{i} [T; N] where i < N` (shared permission)
    let _ = store(i, B, val); 
											    // `A: &{i..N} [u32; N]` (doesn't change as `&{i..N} [u32; N] \ &{i} [T; N]` remains `&{i..N} [T; N]`)
											    // `B: &uniq{i+1..N} [u32; N]` (lose permission at `i`)
    copy_array(i + 1, A, B) // sub-typing gives `&{i..N} [u32; N] <: &{i+1..N} [u32; N]`
  } else {
    ()
  }
```

Add `1` to each element of array from `i` to `N`

```rust
fn increment<const N: usize>(i: u32, A: &uniq{i..N} [u32; N]) =
  let c = i < N;
  if c {
    let val = load(i, A); // `load(i, A)` needs `A: &{i} [T; N] where i < N` (shared permission)
										      // sub-typing gives `&uniq{i..N} [u32; N] <: &uniq{i} [u32; N] <: &{i} [u32; N]`
										      // After load, we have `A: &uniq{i..N} [T; N] \ &{i} [T; N] = &uniq{i+1..N} [T; N]` (ill-defined?)
										      // But store needs `A: &uniq{i} [u32; N]`
										      // The compiler inserts a "fence" here (even though there's already a data dependency here)
    ---
											    // And re-tyck (s0 --- s1) ; s2 under `A: &uniq{i..N} [T; N]` (similar to Dahlia)
    let _ = store(i, A, val + 1);
    increment(i + 1, A)
											    // Now we have `A: &uniq{} [T; N]` (`&uniq{i+1..N} [T; N] ∩ &uniq{} [T; N]`)
  } else {
    ()
  }
```

Now let’s revisit those programs with loop-carried dependence:

read-after-write (RAW)

```rust
// for (j = 1; j < n; j++)
//     S1: a[j] = a[j-1];
// requires: j > 0
fn raw<const N: usize>(j: u32, A: &uniq{j-1..N} [u32; N]) =
  if j < N {
    let v  = load(j-1, A); // `load(j-1, A)` needs `A: &{j-1} [T; N]`
										       // sub-typing gives `&uniq{j-1..N} [u32; N] <: &uniq{j-1} [u32; N] <: &{j-1} [u32; N]`
										       // After load, we have `A: &uniq{j-1..N} [T; N] \ &{j-1} [T; N]`
										       // `= &uniq{j..N} [T; N]`
    let _ = store(j, A, v); // store needs `A: &uniq{j} [u32; N]`
												   // After store, we have `A: &uniq{j..N} [T; N] \ &uniq{j} [T; N] = &uniq{j+1..N} [T; N]`
										       // But recursive call needs `A: &uniq{j..N} [u32; N]`
										       // The compiler inserts a "fence" here
    ---
												   // And re-tyck (s0; s1) --- s2 under `A: &uniq{j-1..N} [T; N]`
    raw(A, j+1, n)
												   // Now we have `A: &uniq{} [T; N]` (`&uniq{j+1..N} [T; N] ∩ &uniq{} [T; N]`)
  } else {
    ()
  }
```

 write-after-read (WAR)

```rust
// for (j = 0; j < n; j++)
//     S1: b[j] = b[j+1];
fn war<const N: usize>(j: u32, B: &uniq{j..N} [u32; N]) =
  if j < N-1 {
    let v = load(j+1, B);  // `load(j+1, B)` needs `B: &{j+1} [T; N]`
                           // subtyping gives `&uniq{j..N} [u32; N] <: &{j+1} [u32; N]`
									         // After load, we have `B: &uniq{j..N} [T; N] \ &{j+1} [T; N]`
										       // `= &uniq{j, j+2..N} [T; N]`
    let _ = store(j, B, v); // `store(j, B, v)` needs `B: &uniq{j} [T; N]`
                            // After store, we have `B: &uniq{j+2..N} [u32; N]`
                            // But recursive call needs `A: &uniq{j+1..N} [u32; N]`
										        // The compiler inserts a "fence" here
    ---
												   // And re-tyck (s0; s1) --- s2 under `B: &uniq{j..N} [u32; N]`
    war(j+1, B)
  } else {
    ()
  }
```

write-after-write (WAW)

```rust
// for (j = 0; j < n; j++) {
//     S1: c[j] = j;  
//     S2: c[j+1] = 5;
// }
fn waw<const N: usize>(j: u32, C: &uniq{j..N} [u32; N]) =
  if j < N-1 {
    let _ = store(j, C, j);   // `store(j, C, j)` needs `C: &uniq{j} [T; N]`
                              // After store, we have `C: &uniq{j+1..N} [u32; N]`
    let _ = store(j+1, C, 5); // `store(j+1, C, 5)` needs `C: &uniq{j+1} [T; N]`
                              // After store, we have `C: &uniq{j+2..N} [u32; N]`
                              // But recursive call needs `C: &uniq{j+1..N} [u32; N]`
                              // The compiler inserts a "fence" here
    ---
                              // And re-tyck (s0; s1) --- s3 under `C: &uniq{j..N} [u32; N]`
    waw(j+1, C) 
  } else {
    ()
  }
```

Matrix-vector multiplication with explicit permissions:

Real Rust code (with `#![feature(generic_const_exprs)]`):

```rust
fn mv_mul<const M: usize, const N: usize>(
    idx: usize,
    a: &[u32; M * N],
    x: &[u32; N],
    y: &mut [u32; M],
) {
    if idx < M {
        let dot_product = cal_dot_product::<M, N>(0, idx, a, x, 0);
        y[idx] = dot_product;
        mv_mul(idx + 1, a, x, y);
    }
}

fn cal_dot_product<const M: usize, const N: usize>(
    j: usize,
    i: usize,
    a: &[u32; M * N],
    x: &[u32; N],
    acc: u32,
) -> u32 {
    if j < N {
        let index = i * N + j;
        cal_dot_product(j + 1, i, a, x, acc + a[index] * x[j])
    } else {
        acc
    }
}
```

L0 With permission:

```rust
fn mv_mul<const M: usize, const N: usize>(
  i: u32, 
  A: &{0..M*N} [u32; M*N],  // Read-only permission for matrix
  X: &{0..N} [u32; N],      // Read-only permission for vector
  Y: &uniq{i..M} [u32; M]   // Unique permission for output vector
) =
  let c = i < M;
  if c {
    // Compute dot product for row i
    let dot_product = cal_dot_product(0, i, A, X, 0);
    let _ = store(i, Y, dot_product);
    mv_mul(i + 1, A, X, Y)
  } else {
    ()
  }

// dot product of row i with vector x
fn cal_dot_product<const M: usize, const N: usize>(
  j: u32,
  i: u32,
  A: &{i*N..(i+1)*N} [u32; M*N],  // Read permission for just this row
  X: &{0..N} [u32; N],             // Read permission for vector
  res: u32
) -> u32 =
  let c = j < N;
  if c {
	  let idx = +(*(i, N), j);
    let a_ij = load(idx, A);
    let x_j = load(j, X);
    let res = +(*(a_ij, x_j), res);
    cal_dot_product(j + 1, i, A, X, res)
  } else {
    res
  }
```

> Compare to Dahlia:
> 
> - dahlia does not guarantee data race free in case of multi-port memory units
>   - dahlia’s type system does not distinguish reads from writes
>   - we are agnostic to number of ports and guarantee data race free noneeless
>     - single-port memory: mem ops would be pipelined (modulo data depeency)
>     - multi-port memory: mem ops would be fully parallelized
> - dahlia does not reason about pipelining
>   - we support auto-pipelining

### Typing L0 programs: the intuition (v.1)

During typing, things like `A: &uniq{i..N} [T; N] \ &{i} [T; N] = &uniq{i+1..N} [T; N]` look ill-defined.
How about separating the ctx into persistent (read, shared) and affine (write, exclusive)?

## L0 Type System Formalization

### Syntax

**Type:**

$$
\begin{aligned}
\text{int} ::= & \;\; \texttt{u8} \mid \texttt{u16} \mid \texttt{u32} \mid \dots \\
\tau ::= & \;\; \texttt{int} \mid \texttt{bool} \mid \texttt{unit} \\
\end{aligned}
$$
<!-- R ::= & \;\; \epsilon \mid i \mid i..i \mid R, \; R \\
i ::= & \;\; n \mid x \mid i + i \mid i - i \mid n * i \\
n ::= & \;\; 0, 1, 2, \ldots \\ -->

<!-- The index expressions `i` for the region are restricted to addition,
subtraction, and multiplication by a constant to keep things simple (and decidable, cf. Presburger arithmetic). -->

**Programs / definitions / expressions:**

$$
\begin{aligned}
P ::= & \;\; D_1 \; \ldots \; D_n \\
D ::= & \;\; \texttt{decl } A : \;  [\texttt{int}; \texttt{ N}] \\
      & \mid \; \texttt{def } f(\vec{x} : \vec{\tau}, \; \overrightarrow{A : 
  \mathsf{uniq@}R \Vert \mathsf{shrd@} R'}) \to \vec{\tau}_o \texttt{ = } E \\
E ::= & \;\mid\; \texttt{let } y \texttt{ = } v; \; E \\
  & \;\mid\; \texttt{let } \vec{y} \texttt{ = } \texttt{op}(\vec{x}); \; E 
  \;\mid\; \texttt{let } \vec{y} \texttt{ = } \texttt{op}(\vec{x}) \text{ ---} \;
  E  \\[6pt]
    
& \;\mid\; \texttt{if } x \; \{ E_1 \} \texttt{ else } \{ E_2 \} 
\;\mid\; x  
\;\mid\; f(\vec{x}) \\
v ::= & \;\; n \;\mid\; \texttt{true} \;\mid\; \texttt{false} \\
R ::= & \;\; \emptyset \;\mid\;  \{rexp\} \;\mid\; R \cup R' \;\mid\; R \setminus
R' \\
rexp ::= & \;\; n \;\mid\; x \;\mid\; rexp + rexp \;\mid\; rexp - rexp \;\mid\;
n * rexp \;\mid\; rexp..rexp \\
\end{aligned}

$$

- `f` and `A` are globally unique identifiers for functions and arrays
- We write `{n1, n2, ..., nk}` for the finite set `{n1} ∪ {n2} ∪ ... ∪ {nk}`
- We write `{n..m}` for the finite set `{x | n ≤ x < m}`
- When we have `A : uniq@{0..N}`, it's equivalent to `A : uniq@{0..N}||shrd@{}`
  (likewise for `shrd`)

**Array:**

We use a Rust-like syntax (`[T; N]`) for arrays, where `T` can be instantiated to any machine integer type, `N` is a compile-time constant.

**Region:**

`R` is finite set of indices for a fixed array `[int; N]`, where 

$R \subseteq \{0, \ldots, N-1\}$.

> Note that `R` may contain free variables from the typing context (e.g., `i..N`
> for some index variable `i`).

**Permission:**

We use the syntax (`shrd` and `uniq`) to represent the (shared or unique)
permission to access arrays. Note that they are not first-class reference types,
but merely a permission decoration on the primitive array type.

**Capability:**

Intuitively, the region+permission-decorated array types represent the
fine-grained *capability* to access an array. For example, if we have `A :
shrd@{0..N}` in the typing context, we have the *read-only*, full *spatial*
capability to access the array `A`; if we have `B : uniq@{0}` in the typing
context, we have the *read-write* capability to access the array `B`, but only
with the index `0`. Finally, if we have `C : uniq@{i..N}||shrd@{N..M}`, we have
the *read-write* capability to access `C` at indices `i, i+1, ..., N-1` and the
*read-only* capability to access `C` at indices `N, N+1, ..., M-1`.

**Op:**

As before, `op` denotes a parametric operator set, with `load` and `store` being two special operators (see below).

### Typing judgement

$$
\Gamma ; \Delta \;\vdash_{\Phi}\; E : \tau 
$$

- $\Gamma$ is the usually variable context
- $\Delta$ is the context for array capability
- $\Phi$ contains lightweight propositions that tracks necessary facts about the array indices.

This judgement reads: under $\Gamma$ and given capabilities in $\Delta$,
the expression `E` has type $\tau$, assuming the facts in $\Phi$.

In general, we require:

- $\text{dom}(\Delta) \bot \text{dom}(\Gamma)$
- $\text{fv}(\Phi) \subseteq \text{dom}(\Gamma)$

<!-- ### Well formed Type

All primitive types (i.e. `int`, `bool`, `unit`) are well-formed. An array type
is well-formed if its size is non-negative. A permission+region-decorated array
type is well-formed w.r.t a typing and a proposition context if we can prove
that the *interpretation* of the region is in-bounds for the array size.

$$
\begin{align*}
&\frac{}{ \cdot ; \cdot  \;\vdash\; \texttt{int} \;\mathsf{Type} } \\[1.2em]
&\frac{}{ \cdot ; \cdot  \;\vdash\; \texttt{bool} \;\mathsf{Type} } \\[1.2em]
&\frac{}{ \cdot ; \cdot \;\vdash\; \texttt{unit} \;\mathsf{Type} } \\[1.2em]
&\frac{ \texttt{N} \geq 0 }
       { \cdot ; \cdot  \;\vdash\; [\texttt{int} ; \texttt{ N}] \;\mathsf{Type} } \\[1.2em]
&\frac{ \text{fv}(\Phi) \subseteq \text{dom}(\Gamma) \quad \text{fv}(R)
\subseteq \text{fv}(\Phi) \quad  \texttt{N} \geq 0 \quad 
\llbracket R \rrbracket_{\Phi} \subseteq \{0, \ldots, \texttt{N}-1\} }
       { \Phi ; \Gamma \;\vdash\; \mathsf{\&}\{R\}[\texttt{int} ; \texttt{ N}] \;\mathsf{Type} } \\[1.2em]
&\frac{ \Phi ; \Gamma \;\vdash\; \mathsf{\&}\{R\}[\texttt{int} ; \texttt{ N}] \;\mathsf{Type}  }
       { \Phi ; \Gamma \;\vdash\; \mathsf{\&uniq}\{R\}[\texttt{int} ; \texttt{ N}] \;\mathsf{Type} }
\end{align*}
$$ -->


<!-- ### Sub-typing

Array types are "contravariant" over their region, i.e., `&{0..N} [T; N] <:
&{1..N} [T; N]` and `&uniq{0..N} [T; N] <: &uniq{0} [T; N]` (greater capability can be used where smaller capability is expected).

$$
\frac{
  \Phi ; \Gamma \;\vdash\; \tau_1 \;\mathsf{Type} \quad
  \Phi ; \Gamma \;\vdash\; \tau_2 \;\mathsf{Type} \quad
  \tau_1 = \tau_2
}{
  \Phi ; \Gamma \;\vdash\; \tau_1 \;<:\; \tau_2
}
$$

$$
\frac{
  \Phi ; \Gamma \;\vdash\; \mathsf{\&}\{R1\}[\texttt{int}; \texttt{ N}] \;\mathsf{Type} \quad
  \Phi ; \Gamma \;\vdash\; \mathsf{\&}\{R2\}[\texttt{int}; \texttt{ N}] \;\mathsf{Type} \quad
  R2 \subseteq R1
}{
  \Phi ; \Gamma \;\vdash\; \mathsf{\&}\{R1\}[\texttt{int}; \texttt{ N}] \;<:\; \mathsf{\&}\{R2\}[\texttt{int}; \texttt{ N}]
}
$$

$$
\frac{
  \Phi ; \Gamma \;\vdash\; \mathsf{\&uniq}\{R1\}[\texttt{int}; \texttt{ N}] \;\mathsf{Type} \quad
  \Phi ; \Gamma \;\vdash\; \mathsf{\&uniq}\{R2\}[\texttt{int}; \texttt{ N}] \;\mathsf{Type} \quad
  R2 \subseteq R1
}{
  \Phi ; \Gamma \;\vdash\; \mathsf{\&uniq}\{R1\}[\texttt{int}; \texttt{ N}] \;<:\; \mathsf{\&uniq}\{R2\}[\texttt{int}; \texttt{ N}]
}
$$ -->

### Resource Algebra

Capability contains fine-grained shared/unique permissions for
  arrays and it forms a PCM (partial commutative monoid):

- The carrier set is a pair $(\mathsf{shrd}, \mathsf{uniq})$, where
  $\mathsf{shrd}$ and $\mathsf{uniq}$ are finite sets of indices
- The validity predicate is defined as:

$$
\text{Valid}((\mathsf{shrd}, \mathsf{uniq})) \;\; \triangleq \;\; \mathsf{shrd} \cap \mathsf{uniq} = \varnothing
$$

- The unit element is $(\varnothing, \varnothing)$
- The composition operation is defined as:

$$
(\mathsf{shrd}_1, \mathsf{uniq}_1) \cdot (\mathsf{shrd}_2, \mathsf{uniq}_2) = 
\begin{cases}
(\mathsf{shrd}_1 \cup \mathsf{shrd}_2, \mathsf{uniq}_1 \cup \mathsf{uniq}_2) & \mathsf{uniq}_1 \cap \mathsf{uniq}_2 = \varnothing \\
& \land \mathsf{uniq}_1 \cap \mathsf{shrd}_2 = \varnothing \\
& \land \mathsf{uniq}_2 \cap \mathsf{shrd}_1 = \varnothing \\
\text{undefined} & \text{otherwise}
\end{cases}
$$

- The composition is commutative and associative
- The carrier set is closed under the inclusion relation $\preceq$:

$$
(\mathsf{shrd}_1, \mathsf{uniq}_1) \preceq (\mathsf{shrd}_2, \mathsf{uniq}_2)
\;\; \triangleq \;\; \text{Valid}((\mathsf{shrd}_1, \mathsf{uniq}_1) \cdot
(\mathsf{shrd}_2, \mathsf{uniq}_2)) \Longrightarrow \text{Valid}((\mathsf{shrd}_1, \mathsf{uniq}_1))
$$

- Unit identity:

$$
(\mathsf{shrd}, \mathsf{uniq}) \cdot (\varnothing, \varnothing) \equiv (\mathsf{shrd}, \mathsf{uniq})
$$

**Partial Order and Difference**

```lean
def c₁ ≤ c₂ := c₁.shrd ⊆ (c₂.shrd ∪ c₂.uniq) ∧ c₁.uniq ⊆ c₂.uniq

def c₁ \ c₂ :=
  if c₂ ≤ c₁ then
    some
      { shrd := c₁.shrd,
        uniq := c₁.uniq \ (c₂.shrd ∪ c₂.uniq),
      }
  else
    none

def Δ₁ ≤ Δ₂ :=
  ∀ A c₁, Δ₁ A = some c₁ →
    ∃ c₂, Δ₂ A = some c₂ 
    ∧ c₁ ≤ c₂

def Δ₁ \ Δ₂ :=
  if Δ₂ ≤ Δ₁ then
    some (λ A,
      match Δ₁ A, Δ₂ A with
      | some c₁, some c₂ => c₁ \ c₂
      | some c₁, none => some c₁
      | none, _ => none
      end)
  else
    none
```

<!-- - Two unique capability `&uniq{R1} [int; N]` `&uniq{R2} [int; N]` compose with disjoint union, iff their regions are disjoint ($R_1 \; \cap \; R_2 = \varnothing$)
- We write $R_1 \; \cdot \; R_2$ (instead of $R_1 \; \uplus \; R_2$) to
  resemble PCM
- We have $\mathsf{\&uniq}\{R1\} [\texttt{int}; \texttt{ N}] \;\cdot\;
  \mathsf{\&uniq}\{R2\} [\texttt{int}; \texttt{ N}] \Longleftrightarrow
  \mathsf{\&uniq}\{R1 \;\cdot\; R2\} [\texttt{int}; \texttt{ N}]$
- We have $\mathsf{\&uniq}\{\} [\texttt{int}; \texttt{ N}]$ as the unit element
- We define $\Delta_1 \; \cdot \; \Delta_2$ as the pointwise
  composition of capabilities in $\Delta_1$ and $\Delta_2$
- A valid $\Delta$ should not contain overlapping regions for the same array
  
$$
\text{Valid}_{\Phi}(\Delta) \;\; \triangleq \;\; \forall A.\;\Biggl( \bigcup_{A : \&uniq\{R1\} \in \Delta} R1 \Biggr) \;\cap\; \Biggl( \bigcup_{A : \&uniq\{R2\} \in \Delta} R2 \Biggr) = \varnothing
$$

**Consistency**

To avoid conflicting capabilities, we require that $\Sigma$ and $\Delta$ are
consistent, i.e., no overlapping regions between read capabilities in $\Sigma$ and
read-write capabilities in $\Delta$.

$$
\text{Consistent}_{\Phi}(\Sigma, \Delta) \;\; \triangleq \;\; \forall A.\;\Biggl( \bigcup_{A : \&\{R\} \in \Sigma} R \Biggr) \;\cap\; \Biggl( \bigcup_{A : \&\text{uniq}\{S\} \in \Delta} S \Biggr) = \varnothing
$$

As regions can contain free variables, validity and consistency are checked
against the propositional context $\Phi$. -->

A Verus formalization of the capability system above.
```rust
pub enum ArrPerm {
    Perm { uniq: Set<int>, shrd: Set<int> },
    Invalid,
}

impl PCM for ArrPerm {
    open spec fn valid(self) -> bool {
        match self {
            ArrPerm::Perm { uniq, shrd } => uniq.disjoint(shrd),
            ArrPerm::Invalid => false,
        }
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (
                ArrPerm::Perm { uniq: u1, shrd: s1 },
                ArrPerm::Perm { uniq: u2, shrd: s2 },
            ) => {
                // Rules:
                //  - uniques must be disjoint
                //  - no uniq may overlap any shared
                if u1.disjoint(u2) 
                // && (u1 + u2).disjoint(s1 + s2) 
                {
                    ArrPerm::Perm { uniq: u1 + u2, shrd: s1 + s2 }
                } else {
                    ArrPerm::Invalid
                }
            },
            _ => ArrPerm::Invalid,
        }
    }

    open spec fn unit() -> Self {
        ArrPerm::Perm { uniq: Set::empty(), shrd: Set::empty() }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
        match (a, b) {
            (
                ArrPerm::Perm { uniq: u1, shrd: s1 },
                ArrPerm::Perm { uniq: u2, shrd: s2 },
            ) => {
                if u1.disjoint(u2) 
                {
                    if (u1 + u2).disjoint(s1 + s2) {
                        assert(a.valid()) by {
                            assume(!(u1.disjoint(s1)));
                            let x = choose|elem: int| u1.contains(elem) && s1.contains(elem);
                            assert((u1 + u2) has x);
                            assert((s1 + s2) has x);
                            assert(!(u1 + u2).disjoint(s1 + s2));
                        }
                    }
                }
            },
            _ => {}
        }
    }

    proof fn commutative(a: Self, b: Self) {
        match (a, b) {
            (
                ArrPerm::Perm { uniq: u1, shrd: s1 },
                ArrPerm::Perm { uniq: u2, shrd: s2 },
            ) => {
                assert(u1.disjoint(u2) == u2.disjoint(u1));
                assert((u1 + u2) == (u2 + u1));
                assert((s1 + s2) == (s2 + s1));
            },
            _ => {}
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        match (a, b, c) {
            (
                ArrPerm::Perm { uniq: u1, shrd: s1 },
                ArrPerm::Perm { uniq: u2, shrd: s2 },
                ArrPerm::Perm { uniq: u3, shrd: s3 },
            ) => {
                assert((u1 + (u2 + u3)) == ((u1 + u2) + u3));
                assert((s1 + (s2 + s3)) == ((s1 + s2) + s3));
            },
            _ => {}
        }
    }

    proof fn op_unit(a: Self) {
        let (uniq_emp, shrd_emp) = (Self::unit()->uniq, Self::unit()->shrd);
        assert(uniq_emp == Set::<int>::empty());
        assert(shrd_emp == Set::<int>::empty());
        match a {
            ArrPerm::Perm { uniq, shrd } => {
                assert(uniq + uniq_emp == uniq);
                assert(shrd + shrd_emp == shrd);
                assert(uniq.disjoint(uniq_emp));
            },
            ArrPerm::Invalid => {
                assert(Self::op(a, Self::unit()) == ArrPerm::Invalid);
            },
        }
    }

    proof fn unit_valid() {
    }
}
```

### Value Typing

$$
\frac{ n \in \texttt{int} }{ \Gamma \;\vdash\; n : \texttt{int} }
$$

$$
\frac{ }{ \Gamma \;\vdash\; \texttt{true} : \texttt{bool} }
$$

$$
\frac{ }{ \Gamma \;\vdash\; \texttt{false} : \texttt{bool} }
$$

$$
\frac{ }{ \Gamma \;\vdash\; \texttt{()} : \texttt{unit} }
$$

<!-- $$
\frac{ \texttt{N} \geq 0 \quad \forall i \in [0, N-1].\; n_i \in \texttt{int} }{ \Gamma \;\vdash\; [n_0, \ldots, n_{N-1}] : [\texttt{int}; \texttt{ N}] }
$$ -->

<!-- ### Coercion

When there is an array in $\Gamma$, we can "coerce" it into full-spatial
capabilities (a read capability in
$\Sigma$ or a read-write capability in $\Delta$), provided that the resulting
contexts are consistent (no conflicting capabilities; no overlapping regions).

$$
\frac{
  \begin{gather*}
  \Gamma(A) = [\texttt{int}; \texttt{ N}] \quad A \not\in \text{dom}(\Sigma)
  \quad A \not\in \text{dom}(\Delta) \\
  \end{gather*}
}{
  \Gamma ; \Delta \;\leadsto_{\Phi, \; \Sigma}\; 
  \Gamma ; \Sigma[A \mapsto \mathsf{\&}\{\texttt{0..N}\}], \Delta
}
$$

$$
\frac{
  \begin{gather*}
  \Gamma(A) = [\texttt{int}; \texttt{ N}] \quad A \not\in \text{dom}(\Delta)
  \quad A \not\in \text{dom}(\Sigma) \\
  \end{gather*}
}{
  \Gamma ; \Delta \;\leadsto_{\Phi, \; \Delta}\;
  \Gamma ; \Sigma, \Delta \;\cdot\; A \mapsto \mathsf{\&uniq}\{\texttt{0..N}\}]
}
$$

$$
\frac{
  \Gamma(A) = [\texttt{int}; \texttt{ N}] \quad A \in \text{dom}(\Sigma) \cup \text{dom}(\Delta)
}{
  \Gamma ; \Delta \;\leadsto_{\Phi, \; \Sigma}\; 
  \Gamma ; \Delta
}
$$

$$
\frac{
  \Gamma(A) = [\texttt{int}; \texttt{ N}] \quad A \in \text{dom}(\Sigma) \cup \text{dom}(\Delta)
}{
  \Gamma ; \Delta \;\leadsto_{\Phi, \; \Delta}\; 
  \Gamma ; \Delta
}
$$

> Together with the expression typing, this auto-coercion will allow, for any array
> `A`
>
> * two parallel `load`s;
> * two parallel (non-overlapping) `store`s;
> * a `store` followed by a parallel (non-conflicting) `load`;
>
> but disallow a `load` followed by a (even non-conflicting) `store`.
> For example: `let x = load(A, i); let _ = store(A, i + 1, 42); ...` won't be
> pipelined (must insert fence).
>
> TODO:
>
> - [ ]  Work around this limitation? -->

### Weakening

As our type system is affine, we can weaken the affine context $\Delta$.

$$
\frac{
  \Gamma ; \Delta \;\vdash_{\Phi}\; E : \tau \quad
}{
  \Gamma ; \Delta \cdot \Delta' \;\vdash_{\Phi}\; E : \tau
}
$$

### Expression Typing

<!-- > Some care is needed to deal with `let A = [0,...,N]; let B = A; ...`. 
> 
> As we
> don't have (and don't aim to support) first-class references, when an array is
> used in an expression (e.g., `load(i, A)`, `store(i, A, v)`, or passed to a
> function), we require that the array is in $\Gamma$ and rely on the
> auto-coercion to promote it to a capability in $\Sigma$ or $\Delta$. In a
> sense, arrays are syntactically "pass by value" but semantically "pass by
> reference".
>
> But this treatment makes it hard to deal with expressions like `let A =
> [0,...,N]; let B = A; ...`. Do we enforce a move semantics or copy semantics
> here? Or do we simply lift all array declarations to the top-level and treat
> them as global arrays? (This is more-or-less what our current type system is assuming.) -->

**Var:**

$$
\frac{
  \Gamma(x) = \tau
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; x : \tau
}
$$

**Let-Val:**

$$
\frac{
  \Gamma \;\vdash\; v : \tau \quad \Gamma[y \mapsto \tau] ; \Delta
  \;\vdash_{\Phi \land (y = v)}\;
E : \tau_E
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; \texttt{let } y \texttt{ = } v; \; E : \tau_E
}
$$

**Pure Op:**

$$
\frac{
  \texttt{op} : \vec{\tau_{i}} \to \vec{\tau_{o}} \quad \Gamma
  (\vec{x}) = \vec{\tau}_i \quad \Gamma[\vec{y} \mapsto \vec{\tau}_o] ;
  \Delta \;\vdash_{\Phi \land (\vec{y} = \texttt{op}(\vec{x}))}\;
E : \tau_E
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; 
  \texttt{let } \vec{y} \texttt{ = } \texttt{op}(\vec{x}); \; E : \tau_E
}
$$

**Load**:

$$
\frac{
  \begin{gather*}
  \Gamma(i) = \texttt{int} \\
  \Phi \vDash 0 \leq i < \texttt{N} \land A \mapsto \mathsf{shrd@}\{i\} \le \Delta \quad \\
  \Gamma[y \mapsto \texttt{int}] ; \Delta \setminus \; A \mapsto  \mathsf{shrd@}\{i\}
  \;\vdash_{\Phi}\;
E : \tau_E
  \end{gather*}
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; 
  \texttt{let } y \texttt{ = } \texttt{load}(A, i); \; E : \tau_E
}
$$

**Store:**

$$
\frac{
  \begin{gather*}
  \Gamma(i) = \texttt{int} \quad
  \Gamma \vdash v : \texttt{int} \\
  \Phi \vDash 0 \leq i < \texttt{N} \land A \mapsto \mathsf{uniq@}\{i\} \le \Delta \quad \\
  \Gamma ; \Delta \setminus \; A \mapsto  \mathsf{uniq@}\{i\}
  \;\vdash_{\Phi}\;
E : \tau_E
  \end{gather*}
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; 
  \texttt{let } \_ \texttt{ = } \texttt{store}(A, i, v); \; E : \tau_E
  
}
$$

**Load-fence:**

$$
\frac{
  \begin{gather*}
  \Gamma(i) = \texttt{int} \\
  \Phi \vDash 0 \leq i < \texttt{N} \land A \mapsto \mathsf{shrd@}\{i\} \le \Delta \quad \\
  \Gamma[y \mapsto \text{int}] ; \Delta
  \;\vdash_{\Phi}\;
E : \tau_E
  \end{gather*}
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; 
  \texttt{let } y \texttt{ = } \texttt{load}(A, i) \text{ ---} \; E : \tau_E
}
$$

**Store-fence:**

$$
\frac{
  \begin{gather*}
  \Gamma(i) = \texttt{int} \quad
  \Gamma \vdash v : \texttt{int} \\
  \Phi \vDash 0 \leq i < \texttt{N} \land A \mapsto \mathsf{uniq@}\{i\} \le \Delta \\
  \Gamma ; \Delta
  \;\vdash_{\Phi}\;
E : \tau_E
  \end{gather*}
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; 
  \texttt{let } \_ \texttt{ = } \texttt{store}(A, i, v) \text{ ---} \; E : \tau_E
}
$$

> TODO: Track separation logic predicates in $\Phi$ for `load` and `store`?

**Conditional:**

$$
\frac{
  \Gamma(x) = \texttt{bool} \quad
  \Gamma ; \Delta \;\vdash_{\Phi \land x}\; E_1 : \tau \quad
  \Gamma ; \Delta \;\vdash_{\Phi \land \lnot x}\; E_2 : \tau
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; 
  \texttt{if } x \; \{ E_1 \} \texttt{ else } \{ E_2 \} : \tau
}
$$

**Function Call:**

$$
\frac{
  \begin{gather*}
  (f \text{ defined}) \\
  \texttt{def } f(\vec{x} : \vec{\tau}_i, \; \overrightarrow{A : 
  \mathsf{uniq@}R \Vert \mathsf{shrd@} R'}) \to \vec{\tau}_o \texttt{ = } E_f\\
  % \Gamma(\vec{y}) <: \overline{\tau_{in}} \quad \\
  \Gamma(\vec{i}) = \vec{\tau}_i \quad
  \Phi \vDash \overrightarrow{A \mapsto \mathsf{uniq@}R[\vec{x} \mapsto \vec{i}] \Vert
  \mathsf{shrd@}R'[\vec{x} \mapsto \vec{i}] \le \Delta} \\
  \Gamma[\vec{y} \mapsto \vec{\tau}_o] ; \Delta \setminus \overrightarrow{A \mapsto \mathsf{uniq@}R[\vec{x} \mapsto \vec{i}] \Vert
  \mathsf{shrd@}R'[\vec{x} \mapsto \vec{i}]}
   \;\vdash_{\Phi}\; E : \tau_E
  \end{gather*}
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; 
  \texttt{let } \vec{y} \texttt{ = } f(\vec{i}, \vec{A}); \; E : \tau_E
}
$$

> TODO: pre-and post-condition for function call?

**Function Call-fence:**

$$
\frac{
  \begin{gather*}
  (f \text{ defined}) \\
  \texttt{def } f(\vec{x} : \vec{\tau}_i, \; \overrightarrow{A : 
  \mathsf{uniq@}R \Vert \mathsf{shrd@} R'}) \to \vec{\tau}_o \texttt{ = } E_f\\
  % \Gamma(\vec{y}) <: \overline{\tau_{in}} \quad \\
  \Gamma(\vec{i}) = \vec{\tau}_i \\
  \Phi \vDash \overrightarrow{A \mapsto \mathsf{uniq@}R[\vec{x} \mapsto \vec{i}] \Vert
  \mathsf{shrd@}R'[\vec{x} \mapsto \vec{i}] \le \Delta} \\
  % \Delta(\vec{Y}) <: \overline{\mathsf{\&uniq}\{R'[\vec{x} \mapsto \vec{y}]\}
  % [\texttt{int}; \texttt{ N}]} \quad 
  \Gamma[\vec{y} \mapsto \vec{\tau}_o] ; \Delta \;\vdash_{\Phi}\; E : \tau_E
  \end{gather*}
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; 
  \texttt{let } \vec{y} \texttt{ = } f(\vec{i}, \vec{A}) \text{ ---}  \; E : \tau_E
}
$$

**Tail Call:**

$$
\frac{
  \begin{gather*}
  (f \text{ defined}) \\
  \texttt{def } f(\vec{x} : \vec{\tau}_i, \; \overrightarrow{A : 
  \mathsf{uniq@}R \Vert \mathsf{shrd@} R'}) \to \vec{\tau}_o \texttt{ = } E_f\\
  % \Gamma(\vec{y}) <: \overline{\tau_{in}} \quad \\
  \Gamma(\vec{i}) = \vec{\tau}_i \\
  \Phi \vDash \overrightarrow{A \mapsto \mathsf{uniq@}R[\vec{x} \mapsto \vec{i}] \Vert
  \mathsf{shrd@}R'[\vec{x} \mapsto \vec{i}] \le \Delta} \\
  % \Delta(\vec{Y}) <: \overline{\mathsf{\&uniq}\{R'[\vec{x} \mapsto \vec{y}]\}
  % [\texttt{int}; \texttt{ N}]} 
  \end{gather*}
}{
  \Gamma ; \Delta \;\vdash_{\Phi}\; 
  f(\vec{i}, \vec{A}) : \vec{\tau}_o
}
$$

### Definition Typing

Global array declarations introduce arrays names in the global typing context $\Pi$.
Function definitions introduce function names in the global typing context
$\Pi$. We require array names and function names to be globally unique.

$$
\frac{
  \begin{gather*}
  \Pi(\vec{A}) = \overrightarrow{\texttt{decl } A: [\texttt{int}; \texttt{ N}]} \\
  % \text{fv}(\Phi) \subseteq \text{dom}(\vec{x_i} \mapsto \overrightarrow{\tau_i}) \\
  \vec{x_i} \mapsto \overrightarrow{\tau_i} \; ; \;
  \overrightarrow{A \mapsto \mathsf{uniq@}R \Vert \mathsf{shrd@} R'} \;\vdash_{\top}\; E_f : \vec{\tau}_o \\
  \end{gather*}
}{
  \Pi
  \;\vdash\;   \texttt{def } f(\vec{x} : \vec{\tau}_i, \; \overrightarrow{A : 
  \mathsf{uniq@}R \Vert \mathsf{shrd@} R'}) \to \vec{\tau}_o \texttt{ = } E
}
$$

<!-- > IDEA:
> Another IR — Parallel L0 (free of data-races)?
>
> - First pass: insert fences to the sequential L0 programs according to the
> typing rules and construct a Parallel L0 program
> - Second pass: compile Parallel L0 to Dataflow graph
> - "Well typed Parallel L0 programs are data-race free" -->

<!-- TODO

- [ ]  Experiment with some Verus embedding?
- [ ]  Another IR — Parallel L0 (free of data-races) -->

### Example Typing Derivation

```python
decl A: [u32; 32]

def increment(i: u32, A: uniq@{i..32}||shrd@{}) -> unit =
  let c = i < 32;
  if c {
    let val = load(i, A)
    ---
    let _ = store(i, A, val + 1);
    let j = i + 1;
    increment(j, A)
  } else {
    ()
  }
```

**Typing derivation for the function body**

$$
\frac{
  \begin{gather*}
  <_{\text{u32}} : (\texttt{u32}, \texttt{u32}) \to \texttt{bool} \quad 
  \frac{
    (i \mapsto \texttt{u32})(i) = \texttt{u32}
  }{
  ... \; ; \; ... \;\vdash_{\top}\; i : \texttt{u32}
  } \quad
  \frac{
  }{
  ... \; ; \; ... \;\vdash_{\top}\; 32 : \texttt{u32}
  }
  \quad
  \frac{ 
    \begin{gather*}
    \frac{
    (i \mapsto \texttt{u32}, c \mapsto \texttt{bool})(c) = \texttt{bool}
  }{
  ... \; ; \; ... \;\vdash_{c = (i < 32)}\; c : \texttt{bool}
  } \quad
    D_{if}
    \quad
    \frac{}{
  ... \; ; \; ... \;\vdash_{c = (i < 32) \land \lnot c}\; () : \texttt{unit}
    }
    \end{gather*}
  }{
    i \mapsto \texttt{u32}, c \mapsto \texttt{bool} \; ; \; ...
      \;\vdash_{c = (i < 32)}\;
  \texttt{if } c \; \{ ... \} \texttt{ else } \{ () \} : \texttt{unit}
  }
  \end{gather*}
}{
  i \mapsto \texttt{u32} \; ; \; A \mapsto \mathsf{uniq@}\{i..32\}
  \Vert
  \mathsf{shrd@}\emptyset
  \;\vdash_{\top}\;
  \texttt{let } c \texttt{ = } i < 32; \;
  \texttt{if } c \; \{ ... \} \texttt{ else } \{ () \} : \texttt{unit}
}
$$

where $D_{if}$ is:

$$
\frac{
  \begin{gather*}
  \frac{
    ...
  }{
  ...
  \vdash_{...}\; 
   i : \texttt{u32}
  }
  \quad
  c = (i < 32) \land c \vDash 0 \leq i < 32 
  \quad
  \frac{
    \begin{gather*}
    \frac{
    ...
  }{
  ...
  \vdash_{...}\; 
   i : \texttt{u32}
  } \quad
  \frac{
    ...
  }{
  ... \vdash_{...}\; 
   val + 1 : \texttt{u32}
  }
  \quad
  ... \vDash ... \land i \in \{i..32\}
  \quad
  D_{rec}
    \end{gather*}
  }{
    ..., val \mapsto \texttt{u32} ; \; A \mapsto \mathsf{uniq@}\{i..32\}
    \Vert \mathsf{shrd@}\emptyset
    \;\vdash_{...}\;
    \texttt{let } \_ \texttt{ = } \texttt{store}(A, i, val + 1) ;\; ... : \texttt{unit}
  }
  \end{gather*}
}{
  i \mapsto \texttt{u32}, c \mapsto \texttt{bool} \; ; \;
  A \mapsto \mathsf{uniq@}\{i..32\}
  \Vert
  \mathsf{shrd@}\emptyset
  \;\vdash_{c = (i < 32) \land c}\;
  \texttt{let } val \texttt{ = } \texttt{load}(A, i) \text{ ---} \;
  ... \; \texttt{store} ... \; ;
  \texttt{increment} ...
  : \texttt{unit}
}
$$

where $D_{rec}$ is:

$$
\quad
  \frac{
    \begin{gather*}
    \texttt{def increment}(i: \texttt{u32}, A: \mathsf{uniq@}\{i..32\} \Vert \mathsf{shrd@}\{\}) \to \texttt{unit} = ... \\
    \frac{...}{... \vdash (i + 1) : \texttt{u32}} \quad
    \frac{
      \begin{gather*}
      \frac{...}{... \vdash j : \texttt{u32}} \quad
      c = (i < 32) \land c \land (j = i + 1) \vDash 
      \{(i+1)..32\} \subseteq \{j..32\} \land \emptyset \subseteq \emptyset
      \end{gather*}
    }{
      ..., j \mapsto \texttt{u32} ; \;
      A \mapsto \mathsf{uniq@}\{(i+1)..32\} \Vert \mathsf{shrd@}\emptyset
      \;\vdash_{... \land (j = i + 1)}\;
      \texttt{increment}(j, A) : \texttt{unit}
    }
    \end{gather*}
  }{
  ... ; \; A \mapsto \mathsf{uniq@}\{i..32\}\setminus \{i\}
    \Vert \mathsf{shrd@}\emptyset
  \;\vdash_{...}\;
  \texttt{let } j \texttt{ = } i + 1; \;
   \texttt{increment}(j, A) : \texttt{unit}
  }
$$

## Operational Semantics

As `L0` is a sequential language, it doesn't make sense for our type soundness
theorem to talk about data races. Instead, we augment the operational semantics
to track the capabilities in the program state and ensure that the capabilities
are used according to the typing rules.

### `L0` Configuration

An `L0` configuration is a tuple $(\Pi, E, \sigma, S, \delta, K)$ where

- $\Pi$ is the function definition context
- $E$ is the current expression being evaluated
- $\sigma$ is the regular variable environment mapping variables to values
- $S$ is the store mapping array names to array values
- $\delta$ tracks the read and write accessess to arrays so far
- $K$ is the call stack, a list of continuation frames

A continuation frame has the form $(\vec{y}, E_{cont}, \sigma_{ret}, \delta_{ret})$ where:
- $\vec{y}$ are the variables to bind the return values to
- $E_{cont}$ is the expression to continue with after the call returns
- $\sigma_{ret}$ is the environment to restore upon return
- $\delta_{ret}$ is the capability state to restore upon return (for fenced calls)

If we have a function definition $\texttt{def } f(\vec{x} : \vec{\tau}_i, \; \overrightarrow{A : 
  \mathsf{uniq@}R \Vert \mathsf{shrd@} R'}) \to \vec{\tau}_o \texttt{ = } E$,
  the initial configuration for evaluating a call to `f` with arguments
  $\vec{v_i}$ and capability $\Delta_{init}$, where
  $\overrightarrow{A \mapsto \mathsf{uniq@}R[\vec{x} \mapsto \vec{v_i}] \Vert
  \mathsf{shrd@}R'[\vec{x} \mapsto \vec{v_i}]} \le \Delta_{init}$,
   is

$$
(\Pi, E, [\vec{x} \mapsto \vec{v_i}], \vec{A} \mapsto [...], \overrightarrow{A \mapsto \mathsf{wt@}\varnothing \Vert \mathsf{rd@}\varnothing}, [])
$$  

### Small-step Operational Semantics

$$
(\Pi, E, \sigma, S, \delta, K) \;\to\; (\Pi, E', \sigma', S', \delta', K')
$$

**Var:**

$$
\frac{
  \sigma(x) = v
}{
  (\Pi, x, \sigma, S, \delta, K) \;\to\; (\Pi, v, \sigma, S, \delta, K)
}
$$

**Pure Op:**

$$
\frac{
  \sigma(\vec{x}) = \vec{v_i} \quad
  \texttt{op}(\vec{v_i}) = \vec{v_o}
}{
  (\Pi, \texttt{let } \vec{y} \texttt{ = } \texttt{op}(\vec{x}); \; E, \sigma, S, \delta, K)
  \;\to\; (\Pi, E, \sigma[\vec{y} \mapsto \vec{v_o}], S, \delta, K)
}
$$

**Load:**

$$
\frac{
  \begin{gather*}
  \sigma(i) = n \quad 0 \leq n < N \quad S(A)[n] = v \\
  \delta(A) = \mathsf{wt@}R \Vert \mathsf{rd@}R' \quad
  n \notin R
  \\
  \delta' = \delta[A \mapsto \mathsf{wt@}R \Vert \mathsf{rd@}R' \cup \{n\}]
  \end{gather*}
}{
  (\Pi, \texttt{let } y \texttt{ = } \texttt{load}(A, i); \; E, \sigma, S, \delta, K)
  \;\to\; (\Pi, E, \sigma[y \mapsto v], S, \delta', K)
}
$$

**Store:**

$$
\frac{
  \begin{gather*}
  \sigma(i) = n  \quad
  0 \leq n < N  \quad \sigma(v) = a_n' \\
  \delta(A) = \mathsf{wt@}R \Vert \mathsf{rd@}R' \quad n \notin R \cup R' \\
  S' = S[A \mapsto [a_0, \ldots, a_{n-1}, a_n', a_{n+1}, \ldots, a_{N-1}]]
  \\
  \delta' = \delta[A \mapsto \mathsf{wt@}R \cup \{n\} \Vert \mathsf{rd@}R']
  \end{gather*}
}{
  (\Pi, \texttt{let } \_ \texttt{ = } \texttt{store}(A, i, v); \; E, \sigma, S, \delta, K)
  \;\to\; (\Pi, E, \sigma, S', \delta', K)
}
$$

**Load-fence:**

$$
\frac{
  \begin{gather*}
\sigma(i) = n \quad 0 \leq n < N \quad S(A)[n] = v \\
  \delta(A) = \mathsf{wt@}R \Vert \mathsf{rd@}R' \quad
  n \notin R
  \\
  \end{gather*}
}{
  (\Pi, \texttt{let } y \texttt{ = } \text{load}(A, i) \text{ ---} \; E, \sigma, S, \delta, K)
  \;\to\; (\Pi, E, \sigma[y \mapsto v], S, \delta, K)
}
$$

**Store-fence:**

$$
\frac{
  \begin{gather*}
  \sigma(i) = n  \quad
  0 \leq n < N  \quad \sigma(v) = a_n' \\
  \delta(A) = \mathsf{wt@}R \Vert \mathsf{rd@}R' \quad n \notin R \cup R' \\
  S' = S[A \mapsto [a_0, \ldots, a_{n-1}, a_n', a_{n+1}, \ldots, a_{N-1}]]
  \\
  \end{gather*}
}{
  (\Pi, \texttt{let } \_ \texttt{ = } \text{store}(A, i, v) \text{ ---} \; E, \sigma, S, \delta, K)
  \;\to\; (\Pi, E, \sigma, S', \delta, K)
}
$$

**Conditional:**

$$
\frac{
  \sigma(x) = \texttt{true} \quad
}{
  (\Pi, \texttt{if } x \; \{ E_1 \} \texttt{ else } \{ E_2 \}, \sigma, S, \delta, K)
  \;\to\; (\Pi, E_1, \sigma, S, \delta, K)
}
$$

$$
\frac{
  \sigma(x) = \texttt{false} \quad
}{
  (\Pi, \texttt{if } x \; \{ E_1 \} \texttt{ else } \{ E_2 \}, \sigma, S, \delta, K)
  \;\to\; (\Pi, E_2, \sigma, S, \delta, K)
}
$$

**Tail Call:**

$$
\frac{
  \begin{gather*}
  \Pi(f) = \texttt{def } f(\vec{x} : \vec{\tau}_i, \; \overrightarrow{A :
  \mathsf{uniq@}R \Vert \mathsf{shrd@} R'}) \to \vec{\tau}_o \texttt{ = } E_f \\
  \sigma(\vec{i}) = \vec{v_i} \quad
  \end{gather*}
}{
  (\Pi, f(\vec{i}, \vec{A}), \sigma, S, \delta, K)
  \;\to\; (\Pi, E_f, [\vec{x} \mapsto \vec{v_i}], S,
  \delta, K)
}
$$

**Non-tail Call:**

$$
\frac{
  \begin{gather*}
  \Pi(f) = \texttt{def } f(\vec{x} : \vec{\tau}_i, \; \overrightarrow{A :
  \mathsf{uniq@}R \Vert \mathsf{shrd@} R'}) \to \vec{\tau}_o \texttt{ = } E_f \\
  \sigma(\vec{i}) = \vec{v_i} \quad
  K' = (\vec{y}, E_{cont}, \sigma, \texttt{none}) :: K
  \end{gather*}
}{
  (\Pi, \texttt{let } \vec{y} \texttt{ = } f(\vec{i}, \vec{A}); \; E_{cont}, \sigma, S, \delta, K)
  \;\to\; (\Pi, E_f, [\vec{x} \mapsto \vec{v_i}], S, \delta, K')
}
$$

**Non-tail Call-fence:**

$$
\frac{
  \begin{gather*}
  \Pi(f) = \texttt{def } f(\vec{x} : \vec{\tau}_i, \; \overrightarrow{A :
  \mathsf{uniq@}R \Vert \mathsf{shrd@} R'}) \to \vec{\tau}_o \texttt{ = } E_f \\
  \sigma(\vec{i}) = \vec{v_i} \quad
  K' = (\vec{y}, E_{cont}, \sigma, \texttt{some }\delta) :: K
  \end{gather*}
}{
  (\Pi, \texttt{let } \vec{y} \texttt{ = } f(\vec{i}, \vec{A}) \text{ ---} \; E_{cont}, \sigma, S, \delta, K)
  \;\to\; (\Pi, E_f, [\vec{x} \mapsto \vec{v_i}], S, \delta, K')
}
$$

**Return:**

$$
\frac{
  \begin{gather*}
  \sigma(\vec{y}_{ret}) = \vec{v}_{ret} \quad
  K = (\vec{y}, E_{cont}, \sigma_{ret}, \texttt{none}) :: K_{rest}
  \end{gather*}
}{
  (\Pi, \vec{y}_{ret}, \sigma, S, \delta, K)
  \;\to\; (\Pi, E_{cont}, \sigma_{ret}[\vec{y} \mapsto \vec{v}_{ret}], S, \delta, K_{rest})
}
$$

**Return-restore:**

$$
\frac{
  \begin{gather*}
  \sigma(\vec{y}_{ret}) = \vec{v}_{ret} \quad
  K = (\vec{y}, E_{cont}, \sigma_{ret}, \texttt{some }\delta_{ret}) :: K_{rest}
  \end{gather*}
}{
  (\Pi, \vec{y}_{ret}, \sigma, S, \delta, K)
  \;\to\; (\Pi, E_{cont}, \sigma_{ret}[\vec{y} \mapsto \vec{v}_{ret}], S, \delta_{ret}, K_{rest})
}
$$
