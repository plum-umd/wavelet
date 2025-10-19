import Wavelet.Semantics.Defs

/-! Definitions to guard a semantics with a given label restriction. -/

namespace Wavelet.Semantics

/-- Modifies labels with a relation. -/
inductive Lts.Guard {S} (P : E → E' → Prop) (lts : Lts S E) : Lts S E' where
  | step : P e e' → lts.Step s e s' → Guard P lts s e' s'

/-- Guards and interprets the labels as another set of operators. -/
def guard
  [Arity Op] [Arity Op']
  (P : Label Op V m n → Label Op' V' m' n' → Prop)
  (sem : Semantics Op V m n) :
  Semantics Op' V' m' n' := {
    S := sem.S,
    init := sem.init,
    lts := sem.lts.Guard P,
  }

/-- Some well-formedness constraints on label guards. -/
class LawfulGuard [Arity Op] [Arity Op']
  (Guard : Label Op V m n → Label Op' V' m' n' → Prop) where
  guard_tau : Guard .τ .τ
  guard_tau_only : ∀ {l}, Guard .τ l → l.isSilent
  guard_input : ∀ {vals l}, Guard (.input vals) l → l.isSilent ∨ l.isInput
  guard_output : ∀ {vals l}, Guard (.output vals) l → l.isSilent ∨ l.isOutput
  guard_yield : ∀ {op inputs outputs l}, Guard (.yield op inputs outputs) l → l.isSilent ∨ l.isYield

/-- Introduces a `Guard` step from a single step in the base LTS. -/
theorem guard_single
  {S : Type u}
  {lts : Lts S E}
  {P : E → E' → Prop}
  {s s' : S}
  (hguard : P e e')
  (hstep : lts.Step s e s') :
  (lts.Guard P).Step s e' s'
:= Lts.Guard.step hguard hstep

/-- `guard` preserves IO-restricted simulation. -/
theorem sim_guard
  [Arity Op] [Arity Op']
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  [InterpConsts V']
  {sem₁ sem₂ : Semantics Op V m n}
  {P : Label Op V m n → Label Op' V' m' n' → Prop}
  [hguard : LawfulGuard P]
  (hsim : sem₁ ≲ᵣ sem₂) :
  sem₁.guard P ≲ᵣ sem₂.guard P
  := by
  apply Lts.Similarity.intro hsim.Sim
  constructor
  · exact hsim.sim_init
  · intros s₁ s₂ l s₁' hR hstep
    simp [Semantics.guard] at hstep
    cases hstep with | step hlabel hstep =>
    rename Label Op V m n => l'
    have ⟨s₂', hstep_s₂, hR₂⟩ := hsim.sim_step _ _ _ _ hR hstep
    exists s₂'
    constructor
    · cases hstep_s₂ with
      | step_yield hstep_yield_s₂ =>
        replace hstep_yield_s₂ := Lts.Guard.step hlabel hstep_yield_s₂
        cases hguard.guard_yield hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (.single hstep_yield_s₂)
        · exact .step_yield hstep_yield_s₂
      | step_input hstep_input_s₂ hstep_tau =>
        replace hstep_input_s₂ := Lts.Guard.step hlabel hstep_input_s₂
        replace hstep_tau := hstep_tau.map (Lts.Guard.step hguard.guard_tau)
        cases hguard.guard_input hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (hstep_tau.prepend hstep_input_s₂)
        · exact .step_input hstep_input_s₂ hstep_tau
      | step_output hstep_tau hstep_output_s₂ =>
        replace hstep_output_s₂ := Lts.Guard.step hlabel hstep_output_s₂
        replace hstep_tau := hstep_tau.map (Lts.Guard.step hguard.guard_tau)
        cases hguard.guard_output hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (hstep_tau.tail hstep_output_s₂)
        · exact .step_output hstep_tau hstep_output_s₂
      | step_tau hstep_tau_s₂ =>
        replace hstep_tau_s₂ := hstep_tau_s₂.map (Lts.Guard.step hguard.guard_tau)
        have := hguard.guard_tau_only hlabel
        cases l <;> simp at this
        exact .step_tau hstep_tau_s₂
    · exact hR₂

end Wavelet.Semantics
