import Wavelet.Thm.Compile.Rewrite.Lemmas

/-!
Helpers for rules after which a channel `o` is no longer used by the rewritten process:
the channels of both processes are equal except `o`, which stays empty after the rewrite.
-/

namespace Wavelet.Compile.DeadCodeElim.UnusedChan

open Semantics Dataflow

/-- Channels are equal except `o`, which is empty in `chans₁`. -/
def EqExcept (o : χ) (chans₀ chans₁ : ChanMap χ V) : Prop :=
  (∀ y, y ≠ o → chans₀ y = chans₁ y) ∧ chans₁ o = []

theorem EqExcept.empty {o : χ} : EqExcept o (ChanMap.empty : ChanMap χ V) .empty :=
  ⟨λ _ _ => rfl, rfl⟩

theorem EqExcept.eq_empty {o : χ} {chans₁ : ChanMap χ V}
  (h : EqExcept o .empty chans₁) : chans₁ = .empty := by
  funext y
  by_cases hy : y = o
  · subst hy; exact h.2
  · exact (h.1 y hy).symm

/-- Popping the same values from channels other than `o` on both sides. -/
theorem EqExcept.pop [DecidableEq χ] {o : χ} {chans₀ chans₁ chans₀' : ChanMap χ V}
  {p : χ → List V}
  (h : EqExcept o chans₀ chans₁)
  (hpop : ∀ y, chans₀ y = p y ++ chans₀' y) (ho : p o = []) :
    ∃ chans₁', (∀ y, chans₁ y = p y ++ chans₁' y) ∧ EqExcept o chans₀' chans₁' := by
  refine ⟨λ y => if y = o then [] else chans₀' y, ?_, ?_, by simp⟩
  · intro y
    by_cases hy : y = o
    · subst hy; simp [h.2, ho]
    · simp [hy, ← h.1 y hy, hpop y]
  · intro y hy
    simp [hy]

/-- Popping from `o` on the original side only. -/
theorem EqExcept.pop_left {o : χ} {chans₀ chans₁ chans₀' : ChanMap χ V} {p : χ → List V}
  (h : EqExcept o chans₀ chans₁)
  (hpop : ∀ y, chans₀ y = p y ++ chans₀' y) (ho : ∀ y, y ≠ o → p y = []) :
    EqExcept o chans₀' chans₁ := by
  refine ⟨λ y hy => ?_, h.2⟩
  rw [← h.1 y hy, hpop y, ho y hy, List.nil_append]

/-- Pushing the same values to channels other than `o` on both sides. -/
theorem EqExcept.push {o : χ} {chans₀ chans₁ : ChanMap χ V} {p₀ p₁ : χ → List V}
  (h : EqExcept o chans₀ chans₁)
  (heq : ∀ y, y ≠ o → p₀ y = p₁ y) (ho : p₁ o = []) :
    EqExcept o (λ y => chans₀ y ++ p₀ y) (λ y => chans₁ y ++ p₁ y) :=
  ⟨λ y hy => by simp only [h.1 y hy, heq y hy], by simp [h.2, ho]⟩

/-- Pushes by the environment or the rest of the graph. -/
theorem EqExcept.frame_push [DecidableEq χ] {o : χ} {chans₀ chans₁ : ChanMap χ V}
  {outs : List χ} {vals : List V}
  (h : EqExcept o chans₀ chans₁) (ho : o ∉ outs) :
    EqExcept o (λ y => chans₀ y ++ ChanMap.pushed outs vals y)
      (λ y => chans₁ y ++ ChanMap.pushed outs vals y) :=
  h.push (λ _ _ => rfl) (ChanMap.pushed_not_mem ho)

end Wavelet.Compile.DeadCodeElim.UnusedChan
