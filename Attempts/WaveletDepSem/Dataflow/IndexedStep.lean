import Wavelet.Dataflow.Proc
import Wavelet.Dataflow.EqMod

/-! An alternative transition system for dataflow that includes
the index of the operator being fired. -/

namespace Wavelet.Dataflow

open Semantics

/-- Steps a configuration by firing an atomic process at a particular index.
This is almost same as the main stepping relation `Config.Step`, but adds more
information to the label. -/
inductive Config.IndexedStep
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  : Lts (Config Op χ V m n) (Nat × Label Op V m n) where
  | step_op
    {c : Config Op χ V _ _}
    {op}
    {inputs : Vector χ (Arity.ι op)}
    {outputs : Vector χ (Arity.ω op)}
    {inputVals outputVals chans'} :
    (_ : i < c.proc.atoms.length) →
    c.proc.atoms[i] = .op op inputs outputs →
    c.chans.popVals inputs = some (inputVals, chans') →
    IndexedStep c (i, .yield op inputVals outputVals) { c with
      chans := chans'.pushVals outputs outputVals,
    }
  | step_async
    {c : Config Op χ V _ _}
    {aop aop' : AsyncOp V}
    {allInputs allOutputs}
    {inputs : Vector χ k₁}
    {inputVals : Vector V k₁}
    {outputs : Vector χ k₂}
    {outputVals : Vector V k₂}
    {chans'}
    {i : Nat} :
    (_ : i < c.proc.atoms.length) →
    c.proc.atoms[i] = .async aop allInputs allOutputs →
    aop.Interp (.mk allInputs allOutputs
      inputs.toList inputVals.toList
      outputs.toList outputVals.toList) aop' →
    c.chans.popVals inputs = some (inputVals, chans') →
    IndexedStep c (i, .τ) { c with
      proc := { c.proc with
        atoms := c.proc.atoms.set i (.async aop' allInputs allOutputs),
      },
      chans := chans'.pushVals outputs outputVals,
    }

theorem Config.IndexedStep.to_step_yield
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  {i : Nat} {op : Op}
  {inputs : Vector V (Arity.ι op)}
  {outputs : Vector V (Arity.ω op)}
  (hstep : Config.IndexedStep c (i, .yield op inputs outputs) c') :
    Config.Step c (.yield op inputs outputs) c'
  := by
  cases hstep with | step_op _ hget hpop =>
  exact .step_op (by rw [← hget]; simp) hpop

theorem Config.IndexedStep.from_step_yield
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  {op : Op}
  {inputs : Vector V (Arity.ι op)}
  {outputs : Vector V (Arity.ω op)}
  (hstep : Config.Step c (.yield op inputs outputs) c') :
    ∃ i, Config.IndexedStep c (i, .yield op inputs outputs) c'
  := by
  cases hstep with | step_op hmem hpop =>
  have ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  exists i
  exact .step_op hi hget hpop

theorem Config.IndexedStep.iff_step_yield
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  {op : Op}
  {inputs : Vector V (Arity.ι op)}
  {outputs : Vector V (Arity.ω op)} :
    (∃ i, Config.IndexedStep c (i, .yield op inputs outputs) c') ↔
    Config.Step c (.yield op inputs outputs) c'
  := by
  constructor
  · simp only [forall_exists_index]
    intros i
    apply Config.IndexedStep.to_step_yield
  · exact Config.IndexedStep.from_step_yield

theorem Config.IndexedStep.to_step_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  {i : Nat}
  (hstep : Config.IndexedStep c (i, .τ) c') :
    Config.Step c .τ c'
  := by
  cases hstep with | step_async hi hget hinterp hpop =>
  exact .step_async hi hget hinterp hpop

theorem Config.IndexedStep.from_step_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  (hstep : Config.Step c .τ c') :
    ∃ i, Config.IndexedStep c (i, .τ) c'
  := by
  cases hstep with | step_async hi hget hinterp hpop =>
  exact ⟨_, .step_async hi hget hinterp hpop⟩

theorem Config.IndexedStep.iff_step_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n} :
    (∃ i, Config.IndexedStep c (i, .τ) c') ↔
    Config.Step c .τ c'
  := by
  constructor
  · simp only [forall_exists_index]
    intros i
    apply Config.IndexedStep.to_step_tau
  · exact Config.IndexedStep.from_step_tau

theorem Config.IndexedStep.from_step_yield_or_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : Config.Step c l c') :
    ∃ i, Config.IndexedStep c (i, l) c'
  := by
  cases l <;> simp at hl
  · have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, hstep'⟩
  · have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_tau hstep
    exact ⟨i, hstep'⟩

theorem Config.IndexedStep.to_step_yield_or_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  {l : Label Op V m n}
  (hstep : Config.IndexedStep c (i, l) c') :
    Config.Step c l c'
  := by
  cases l with
  | yield => exact Config.IndexedStep.to_step_yield hstep
  | τ => exact Config.IndexedStep.to_step_tau hstep
  | _ => cases hstep

theorem Config.IndexedStep.iff_step_yield_or_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent) :
    (∃ i, Config.IndexedStep c (i, l) c') ↔ Config.Step c l c'
  := by
  constructor
  · intros h
    have ⟨i, h⟩ := h
    exact Config.IndexedStep.to_step_yield_or_tau h
  · intros h
    apply Config.IndexedStep.from_step_yield_or_tau hl h

theorem Config.IndexedStep.unique_label_mod_outputs
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c₁ c₂ : Config Op χ V m n}
  {l₁ l₂ : Label Op V m n}
  (hstep₁ : Config.IndexedStep c (i, l₁) c₁)
  (hstep₂ : Config.IndexedStep c (i, l₂) c₂) :
    Label.EqModYieldOutputs l₁ l₂
  := by
  cases hstep₁ <;> rename_i hget₁ <;>
  cases hstep₂ <;> rename_i hget₂
  all_goals simp [hget₁] at hget₂
  case step_op.step_op =>
    rename_i hpop₁ _ _ _ _ _ _ _ hpop₂ _
    have ⟨h₁, h₂, h₃⟩ := hget₂
    subst h₁; subst h₂; subst h₃
    simp [hpop₁] at hpop₂
    have ⟨h₁, h₂⟩ := hpop₂
    subst h₁; subst h₂
    simp [Label.EqModYieldOutputs]
  simp [Label.EqModYieldOutputs]

theorem Config.IndexedStep.unique_index_mod
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {EqV : V → V → Prop} [IsRefl V EqV]
  {c c₁ c₂ : Config Op χ V m n}
  {l₁ l₂ : Label Op V m n}
  (hstep₁ : Config.IndexedStep c (i, l₁) c₁)
  (hstep₂ : Config.IndexedStep c (i, l₂) c₂)
  (hdet : Label.IsYieldOrSilentAndDetMod EqV l₁ l₂) :
    Label.EqMod EqV l₁ l₂ ∧ Config.EqMod EqV c₁ c₂
  := by
  cases hstep₁ <;> rename_i hget₁ <;>
  cases hstep₂ <;> rename_i hget₂
  all_goals simp [hget₁] at hget₂
  case step_op.step_op =>
    rename_i hpop₁ _ _ _ _ _ _ _ hpop₂ _
    have ⟨h₁, h₂, h₃⟩ := hget₂
    subst h₁; subst h₂; subst h₃
    simp [hpop₁] at hpop₂
    have ⟨h₁, h₂⟩ := hpop₂
    subst h₁; subst h₂
    simp [Label.IsYieldOrSilentAndDetMod] at hdet
    constructor
    · simp [Label.EqMod, IsRefl.refl]
      apply hdet
      all_goals rfl
    · simp [Config.EqMod, IsRefl.refl]
      have := hdet rfl rfl
      apply congr_eq_mod_push_vals_alt
      exact this
  case step_async.step_async =>
    rename_i aop _ _ _ inputs₁ inputVals₁ outputs₁ outputVals₁ _ hinterp₁ hpop₁ _ _ _ _ _ _ _
      inputs₂ inputVals₂ outputs₂ outputVals₂ _ hinterp₂ hpop₂ hget₂
    have ⟨h₁, h₂, h₃⟩ := hget₂
    subst h₁; subst h₂; subst h₃
    have heq_inputs := AsyncOp.Interp.det_inputs hinterp₁ hinterp₂
    have ⟨h₁, h₂⟩ := Vector.toList_inj_heq heq_inputs
    subst h₁; subst h₂
    simp [hpop₁] at hpop₂
    have ⟨h₁, h₂⟩ := hpop₂
    subst h₁; subst h₂
    have ⟨h₁, h₂, h₃, h₄⟩ := AsyncOp.Interp.det_outputs hinterp₁ hinterp₂ rfl
    replace ⟨h₂, h₂'⟩ := Vector.toList_inj_heq h₂
    subst h₂; subst h₂'
    replace h₃ := Vector.toList_inj.mp h₃
    subst h₃
    subst h₄
    exact ⟨
      by apply IsRefl.refl,
      by apply IsRefl.refl,
    ⟩

theorem Config.IndexedStep.unique_index
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c₁ c₂ : Config Op χ V m n}
  {l₁ l₂ : Label Op V m n}
  (hstep₁ : Config.IndexedStep c (i, l₁) c₁)
  (hstep₂ : Config.IndexedStep c (i, l₂) c₂)
  (hdet : Label.IsYieldOrSilentAndDet l₁ l₂) :
    l₁ = l₂ ∧ c₁ = c₂
  := by
  have := Config.IndexedStep.unique_index_mod (EqV := Eq) hstep₁ hstep₂
  simp at this
  apply this hdet

theorem Config.IndexedStep.unique_index_alt
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c₁ c₂ : Config Op χ V m n}
  {l : Label Op V m n}
  (hstep₁ : Config.IndexedStep c (i, l) c₁)
  (hstep₂ : Config.IndexedStep c (i, l) c₂)
  (hl : l.isYield ∨ l.isSilent) :
    c₁ = c₂
  := by
  apply (Config.IndexedStep.unique_index hstep₁ hstep₂ _).2
  cases l <;> simp [Label.IsYieldOrSilentAndDet, Label.Deterministic] at hl ⊢
  grind only

theorem Config.IndexedStep.same_label_kind
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c₁ c₂ c₃ : Config Op χ V m n}
  {l₁ l₂ l₃ : Label Op V m n}
  (hstep₁ : Config.IndexedStep c (i, l₁) c₁)
  (hstep₂ : Config.IndexedStep c₁ (j, l₂) c₂)
  (hstep₃ : Config.IndexedStep c (j, l₃) c₃) :
    l₂.isYield ↔ l₃.isYield
  := by
  cases hstep₁ <;> cases hstep₂ <;> cases hstep₃
  any_goals simp
  any_goals grind only [= List.length_set, =_ Vector.toList_toArray,
    = List.getElem_set, cases Or]

end Wavelet.Dataflow
