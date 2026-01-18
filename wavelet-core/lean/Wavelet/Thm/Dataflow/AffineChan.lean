import Wavelet.Dataflow.AffineChan

import Wavelet.Thm.Semantics.Invariant

namespace Wavelet.Dataflow

open Semantics

/-- `AffineChan` is a state invariant. -/
theorem Proc.AffineChan.inv
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {s : Config Op χ V m n}
  (haff : s.proc.AffineChan) :
    Config.Step.IsInvariantAt (·.proc.AffineChan) s
  := by
  apply Lts.IsInvariantAt.by_induction
  · exact haff
  · intros s₁ s₂ l hinv hstep
    cases hstep with
    | step_async _ hget hinterp _ =>
      rename Nat => i
      simp [Proc.AffineChan]
      have ⟨h₁, h₂, ⟨h₃₁, h₃₂⟩, h₄, h₅⟩ := hinv
      simp [h₁, h₂]
      and_intros
      · intros j
        rcases j with ⟨j, hlt⟩
        simp at hlt
        by_cases h₁ : i = j
        · subst h₁
          have := h₃₁ ⟨i, by omega⟩
          simp [AtomicProc.inputs, AtomicProc.outputs, hget] at this ⊢
          exact this
        · simp [h₁]
          apply h₃₁ ⟨j, hlt⟩
      · intros j k hne
        rcases j with ⟨j, hj⟩
        rcases k with ⟨k, hk⟩
        simp at hj hk hne
        have := h₃₂ ⟨j, hj⟩ ⟨k, hk⟩ (by simp [hne])
        simp at this
        grind [AtomicProc.inputs, AtomicProc.outputs]
      · intros ap hmem_ap
        have := List.mem_or_eq_of_mem_set hmem_ap
        cases this with
        | inl hmem_ap =>
          exact h₄ ap hmem_ap
        | inr heq_ap =>
          subst heq_ap
          have := h₄ _ (List.mem_of_getElem hget)
          exact this
      · intros ap hmem_ap
        have := List.mem_or_eq_of_mem_set hmem_ap
        cases this with
        | inl hmem_ap =>
          exact h₅ ap hmem_ap
        | inr heq_ap =>
          subst heq_ap
          have := h₅ _ (List.mem_of_getElem hget)
          exact this
    | _ => simp [hinv]

end Wavelet.Dataflow
