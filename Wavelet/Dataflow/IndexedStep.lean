import Wavelet.Dataflow.Proc

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
  (hl : l.isYield ∨ l.isSilent)
  (hstep : Config.IndexedStep c (i, l) c') :
    Config.Step c l c'
  := by
  cases l <;> simp at hl
  · exact Config.IndexedStep.to_step_yield hstep
  · exact Config.IndexedStep.to_step_tau hstep

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
    exact Config.IndexedStep.to_step_yield_or_tau hl h
  · intros h
    apply Config.IndexedStep.from_step_yield_or_tau hl h

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
    simp [Label.IsYieldOrSilentAndDet] at hdet
    constructor
    all_goals
      congr
      apply hdet
      all_goals rfl
  case step_async.step_async =>
    rename_i aop _ _ _ inputs₁ inputVals₁ outputs₁ outputVals₁ _ hinterp₁ hpop₁ _ _ _ _ _ _ _
      inputs₂ inputVals₂ outputs₂ outputVals₂ _ hinterp₂ hpop₂ hget₂
    have ⟨h₁, h₂, h₃⟩ := hget₂
    subst h₁; subst h₂; subst h₃
    have := async_op_interp_det_inputs_len hinterp₁ hinterp₂
    simp at this
    subst this
    cases aop with
    | merge =>
      generalize hinputs₁' : inputs₁.toList = inputs₁'
      generalize hinputs₂' : inputs₂.toList = inputs₂'
      generalize houtputs₁' : outputs₁.toList = outputs₁'
      generalize houtputs₂' : outputs₂.toList = outputs₂'
      generalize hinputVals₁' : inputVals₁.toList = inputVals₁'
      generalize hinputVals₂' : inputVals₂.toList = inputVals₂'
      generalize houtputVals₁' : outputVals₁.toList = outputVals₁'
      generalize houtputVals₂' : outputVals₂.toList = outputVals₂'
      rw [hinputs₁', hinputVals₁', houtputs₁', houtputVals₁'] at hinterp₁
      rw [hinputs₂', hinputVals₂', houtputs₂', houtputVals₂'] at hinterp₂
      cases hinterp₁ <;> cases hinterp₂
      all_goals
        have := pop_vals_eq_head hinputs₁' hinputs₂' hpop₁ hpop₂
        simp [hinputVals₁', hinputVals₂'] at this
        subst this
      case merge.interp_merge_true.interp_merge_true |
        merge.interp_merge_false.interp_merge_false =>
        simp [← houtputs₁'] at houtputs₂'
        have ⟨h₁, h₂⟩ := Vector.toList_inj_heq houtputs₂'
        subst h₁; subst h₂
        simp [← hinputs₁'] at hinputs₂'
        have := Vector.toList_inj.mp hinputs₂'
        subst this
        simp [hpop₁] at hpop₂
        have ⟨h₁, h₂⟩ := hpop₂
        subst h₁; subst h₂
        simp [hinputVals₁'] at hinputVals₂'
        subst hinputVals₂'
        simp [← houtputVals₁'] at houtputVals₂'
        have := Vector.toList_inj.mp houtputVals₂'
        subst this
        exact ⟨rfl, rfl⟩
      all_goals grind only
    | _ =>
      have heq_inputs := async_op_interp_det_inputs_except_merge hinterp₁ hinterp₂ (by simp)
      have := Vector.toList_inj.mp heq_inputs
      subst this
      simp [hpop₁] at hpop₂
      have ⟨h₁, h₂⟩ := hpop₂
      subst h₁; subst h₂
      have ⟨h₁, h₂, h₃⟩ := async_op_interp_det_outputs hinterp₁ hinterp₂ rfl rfl
      have ⟨h₁, h₁'⟩ := Vector.toList_inj_heq h₁
      subst h₁; subst h₁'
      replace h₂ := Vector.toList_inj.mp h₂
      subst h₂
      subst h₃
      exact ⟨rfl, rfl⟩

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
