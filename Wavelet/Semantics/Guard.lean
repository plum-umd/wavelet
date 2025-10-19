import Wavelet.Semantics.Defs

/-! Definitions to guard a semantics with a given state or label invariant. -/

namespace Wavelet.Semantics

/-- Restricts an LTS by imposing a state invariant. -/
inductive Lts.GuardState {S} (Inv : S → Prop) (lts : Lts S E) : Lts S E where
  | step : Inv s → Inv s' → lts.Step s e s' → GuardState Inv lts s e s'

/-- Guards the transition of a semantics with the given invariant. -/
def guardState
  [Arity Op]
  (sem : Semantics Op V m n)
  (Inv : sem.S → Prop) :
  Semantics Op V m n :=
  {
    S := sem.S,
    init := sem.init,
    lts := sem.lts.GuardState Inv,
  }

/-- Modifies labels with a relation. -/
inductive Lts.GuardLabel {S} (Guard : E → E' → Prop) (lts : Lts S E) : Lts S E' where
  | step : Guard e e' → lts.Step s e s' → GuardLabel Guard lts s e' s'

/-- Guards and interprets the labels as another set of operators. -/
def guardLabel
  [Arity Op] [Arity Op']
  (sem : Semantics Op V m n)
  (Guard : Label Op V m n → Label Op' V' m' n' → Prop) :
  Semantics Op' V' m' n' := {
    S := sem.S,
    init := sem.init,
    lts := sem.lts.GuardLabel Guard,
  }

/-- Combines `GuardState` and `GuardLabel`. -/
def Lts.Guard {S}
  (lts : Lts S E)
  (Inv : S → Prop)
  (Guard : E → E' → Prop) : Lts S E' :=
  (lts.GuardState Inv).GuardLabel Guard

/-- Combines `guardState` and `guardLabel`. -/
def guard
  [Arity Op] [Arity Op']
  (sem : Semantics Op V m n)
  (Inv : sem.S → Prop)
  (Guard : Label Op V m n → Label Op' V' m' n' → Prop) :
  Semantics Op' V' m' n' :=
  (sem.guardState Inv).guardLabel Guard

/-- Some well-formedness constraints on label guards. -/
class LawfulLabelGuard [Arity Op] [Arity Op']
  (Guard : Label Op V m n → Label Op' V' m' n' → Prop) where
  label_guard_tau : Guard .τ .τ
  label_guard_tau_only : ∀ {l}, Guard .τ l → l.isSilent
  label_guard_input : ∀ {vals l}, Guard (.input vals) l → l.isSilent ∨ l.isInput
  label_guard_output : ∀ {vals l}, Guard (.output vals) l → l.isSilent ∨ l.isOutput
  label_guard_yield : ∀ {op inputs outputs l}, Guard (.yield op inputs outputs) l → l.isSilent ∨ l.isYield

/-- Introduces a `Guard` step from a single step in the base LTS. -/
theorem guard_single
  {S : Type u}
  {lts : Lts S E}
  {Inv : S → Prop}
  {Guard : E → E' → Prop}
  {s s' : S}
  (hstep : lts.Step s e s')
  (hinv₁ : Inv s)
  (hinv₂ : Inv s')
  (hinterp : Guard e e') :
  (lts.Guard Inv Guard).Step s e' s'
:= by
  apply Lts.GuardLabel.step hinterp
  apply Lts.GuardState.step hinv₁ hinv₂ hstep

/-- `guardLabel` preserves IO-restricted simulation. -/
theorem sim_guard_label
  [Arity Op] [Arity Op']
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  [InterpConsts V']
  {sem₁ sem₂ : Semantics Op V m n}
  {Guard : Label Op V m n → Label Op' V' m' n' → Prop}
  [hguard : LawfulLabelGuard Guard]
  (hsim : sem₁ ≲ᵣ sem₂) :
  sem₁.guardLabel Guard ≲ᵣ sem₂.guardLabel Guard
  := by
  apply Lts.Similarity.intro hsim.Sim
  constructor
  · exact hsim.sim_init
  · intros s₁ s₂ l s₁' hR hstep
    simp [Semantics.guardLabel] at hstep
    cases hstep with | step hlabel hstep =>
    rename Label Op V m n => l'
    have ⟨s₂', hstep_s₂, hR₂⟩ := hsim.sim_step _ _ _ _ hR hstep
    exists s₂'
    constructor
    · cases hstep_s₂ with
      | step_yield hstep_yield_s₂ =>
        replace hstep_yield_s₂ := Lts.GuardLabel.step hlabel hstep_yield_s₂
        cases hguard.label_guard_yield hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (.single hstep_yield_s₂)
        · exact .step_yield hstep_yield_s₂
      | step_input hstep_input_s₂ hstep_tau =>
        replace hstep_input_s₂ := Lts.GuardLabel.step hlabel hstep_input_s₂
        replace hstep_tau := hstep_tau.map (Lts.GuardLabel.step hguard.label_guard_tau)
        cases hguard.label_guard_input hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (hstep_tau.prepend hstep_input_s₂)
        · exact .step_input hstep_input_s₂ hstep_tau
      | step_output hstep_tau hstep_output_s₂ =>
        replace hstep_output_s₂ := Lts.GuardLabel.step hlabel hstep_output_s₂
        replace hstep_tau := hstep_tau.map (Lts.GuardLabel.step hguard.label_guard_tau)
        cases hguard.label_guard_output hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (hstep_tau.tail hstep_output_s₂)
        · exact .step_output hstep_tau hstep_output_s₂
      | step_tau hstep_tau_s₂ =>
        replace hstep_tau_s₂ := hstep_tau_s₂.map (Lts.GuardLabel.step hguard.label_guard_tau)
        have := hguard.label_guard_tau_only hlabel
        cases l <;> simp at this
        exact .step_tau hstep_tau_s₂
    · exact hR₂

end Wavelet.Semantics
