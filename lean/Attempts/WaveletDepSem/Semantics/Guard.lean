import Wavelet.Semantics.Defs

/-! Definitions to guard a semantics with a given label restriction. -/

namespace Wavelet.Semantics

/-- Modifies labels with a relation. -/
inductive Lts.GuardStep {S} (P : E → E' → Prop) (lts : Lts S E) : Lts S E' where
  | step : P e e' → lts.Step s e s' → GuardStep P lts s e' s'

/-- Guards and interprets the labels as another set of operators. -/
def guard
  [Arity Op] [Arity Op']
  (P : Label Op V m n → Label Op' V' m' n' → Prop)
  (sem : Semantics S Op V m n) :
  Semantics S Op' V' m' n' := {
    init := sem.init,
    lts := sem.lts.GuardStep P,
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
  (lts.GuardStep P).Step s e' s'
:= Lts.GuardStep.step hguard hstep

theorem guard_tau_star
  {lts : Lts C E}
  {P : E → E' → Prop}
  (hsteps : lts.TauStar τ s₁ s₁')
  (hguard : P τ τ') : (lts.GuardStep P).TauStar τ' s₁ s₁'
  := by
  induction hsteps with
  | refl => exact .refl
  | tail pref tail ih =>
    have := Lts.GuardStep.step hguard tail
    exact .tail ih this

theorem Guard.map_step
  {S}
  {lts₁ lts₂ : Lts S E}
  {P : E → E' → Prop}
  {s s' : S}
  (hmap : ∀ {s s' l}, lts₁.Step s l s' → lts₂.Step s l s') :
    (lts₁.GuardStep P).Step s l s' → (lts₂.GuardStep P).Step s l s'
  | .step hguard hstep => .step hguard (hmap hstep)

theorem Guard.map_guard
  {S}
  {lts : Lts S E}
  {P₁ P₂ : E → E' → Prop}
  {s s' : S}
  (hmap : ∀ {l₁ l₂}, P₁ l₁ l₂ → P₂ l₁ l₂) :
    (lts.GuardStep P₁).Step s l s' → (lts.GuardStep P₂).Step s l s'
  | .step hguard hstep => .step (hmap hguard) hstep

/-- `guard` preserves IO-restricted simulation. -/
theorem sim_guard
  [Arity Op] [Arity Op']
  [InterpConsts V]
  [InterpConsts V']
  {sem₁ sem₂ : Semantics S Op V m n}
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
        replace hstep_yield_s₂ := Lts.GuardStep.step hlabel hstep_yield_s₂
        cases hguard.guard_yield hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (.single hstep_yield_s₂)
        · exact .step_yield hstep_yield_s₂
      | step_input hstep_input_s₂ hstep_tau =>
        replace hstep_input_s₂ := Lts.GuardStep.step hlabel hstep_input_s₂
        replace hstep_tau := hstep_tau.map (Lts.GuardStep.step hguard.guard_tau)
        cases hguard.guard_input hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (hstep_tau.prepend hstep_input_s₂)
        · exact .step_input hstep_input_s₂ hstep_tau
      | step_output hstep_tau hstep_output_s₂ =>
        replace hstep_output_s₂ := Lts.GuardStep.step hlabel hstep_output_s₂
        replace hstep_tau := hstep_tau.map (Lts.GuardStep.step hguard.guard_tau)
        cases hguard.guard_output hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (hstep_tau.tail hstep_output_s₂)
        · exact .step_output hstep_tau hstep_output_s₂
      | step_tau hstep_tau_s₂ =>
        replace hstep_tau_s₂ := hstep_tau_s₂.map (Lts.GuardStep.step hguard.guard_tau)
        have := hguard.guard_tau_only hlabel
        cases l <;> simp at this
        exact .step_tau hstep_tau_s₂
    · exact hR₂

/-- `guard` preserves weak simulation. -/
theorem sim_weak_guard
  [Arity Op] [Arity Op']
  [InterpConsts V]
  [InterpConsts V']
  {sem₁ sem₂ : Semantics S Op V m n}
  {P : Label Op V m n → Label Op' V' m' n' → Prop}
  [hguard : LawfulGuard P]
  (hsim : sem₁ ≲ sem₂) :
  sem₁.guard P ≲ sem₂.guard P
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
      | refl =>
        have := hguard.guard_tau_only hlabel
        cases l <;> simp at this
        exact .refl
      | step htau₁ hstep₂ htau₂ =>
        rename_i s₂₁ s₂₂
        apply Lts.WeakStep.step
        · exact guard_tau_star htau₁ hguard.guard_tau
        · exact Lts.GuardStep.step hlabel hstep₂
        · exact guard_tau_star htau₂ hguard.guard_tau
    · exact hR₂

theorem sim_guard_imp
  [Arity Op] [Arity Op']
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  [InterpConsts V']
  {sem : Semantics S Op V m n}
  {P₁ : Label Op V m n → Label Op' V' m' n' → Prop}
  {P₂ : Label Op V m n → Label Op' V' m' n' → Prop}
  (himp : ∀ {l₁ l₂}, P₁ l₁ l₂ → P₂ l₁ l₂) :
  sem.guard P₁ ≲ₛ sem.guard P₂
  := by
  apply Lts.Similarity.intro Eq
  constructor
  · rfl
  · intros s₁ s₂ l s₁' hR hstep
    exists s₁'
    subst hR
    simp
    replace ⟨hp, hstep⟩ := hstep
    exact ⟨himp hp, hstep⟩

end Wavelet.Semantics
