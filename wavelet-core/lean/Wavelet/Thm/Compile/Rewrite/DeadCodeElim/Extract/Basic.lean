import Wavelet.Thm.Compile.Rewrite.Monad

/-!
Helper lemmas for extracting `DCEMatch` from successful runs of `deadCodeElim`.

The `branch_*_some` lemmas in `Extract/*.lean` each symbolically execute one
top-level branch of `deadCodeElim`. Their hypothesis `h` restates the body of
the branch verbatim (so it must be kept in sync with `Wavelet.Compile.Rewrite`);
`deadCodeElim_some` applies them by `exact`, which checks that they match.
-/

namespace Wavelet.Compile.DeadCodeElim.Extract

theorem length_eq_two {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with | [a, b], _ => exact ⟨a, b, rfl⟩

theorem length_eq_three {l : List α} (h : l.length = 3) : ∃ a b c, l = [a, b, c] := by
  match l, h with | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

theorem ne_of_not_mem_singleton {i j : Nat} (h : i ∉ [j]) : i ≠ j := by
  simpa using h

theorem ne_of_not_mem_pair {i j k : Nat} (h : i ∉ [j, k]) : i ≠ j ∧ i ≠ k := by
  simpa using h

end Wavelet.Compile.DeadCodeElim.Extract
