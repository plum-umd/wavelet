import Wavelet.Dataflow.Proc

/-! An alternative transition system for dataflow that includes
the index of the operator being fired. -/

namespace Wavelet.Dataflow

open Semantics

inductive IndexedLabel Op V [Arity Op] where
  | yield (op : Op) (inputs : Vector V (Arity.ι op)) (outputs : Vector V (Arity.ω op))
  | internal (aop : AsyncOp V)

/-- Steps a configuration by firing an atomic process at a particular index.
This is almost same as the main stepping relation `Config.Step`, but adds more
information to the label. -/
inductive Config.IndexedStep
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  : Lts (Config Op χ V m n) (Nat × IndexedLabel Op V) where
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
    IndexedStep c (i, .internal aop) { c with
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
  {i : Nat} {aop : AsyncOp V}
  (hstep : Config.IndexedStep c (i, .internal aop) c') :
    Config.Step c .τ c'
  := by
  cases hstep with | step_async hi hget hinterp hpop =>
  exact .step_async hi hget hinterp hpop

theorem Config.IndexedStep.from_step_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  (hstep : Config.Step c .τ c') :
    ∃ i aop, Config.IndexedStep c (i, .internal aop) c'
  := by
  cases hstep with | step_async hi hget hinterp hpop =>
  exact ⟨_, _, .step_async hi hget hinterp hpop⟩

theorem Config.IndexedStep.iff_step_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n} :
    (∃ i aop, Config.IndexedStep c (i, .internal aop) c') ↔
    Config.Step c .τ c'
  := by
  constructor
  · simp only [forall_exists_index]
    intros i aop
    apply Config.IndexedStep.to_step_tau
  · exact Config.IndexedStep.from_step_tau

theorem Config.IndexedStep.from_step_yield_or_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : Config.Step c l c') :
    ∃ i l', Config.IndexedStep c (i, l') c'
  := by
  cases l <;> simp at hl
  · have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, _, hstep'⟩
  · have ⟨i, _, hstep'⟩ := Config.IndexedStep.from_step_tau hstep
    exact ⟨i, _, hstep'⟩

theorem Config.IndexedStep.to_step_yield_or_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n}
  {l : IndexedLabel Op V}
  (hstep : Config.IndexedStep c (i, l) c') :
    ∃ l', (l'.isYield ∨ l'.isSilent) ∧ Config.Step c l' c'
  := by
  cases l
  · exact ⟨_, by simp, Config.IndexedStep.to_step_yield hstep⟩
  · exact ⟨_, by simp, Config.IndexedStep.to_step_tau hstep⟩

theorem Config.IndexedStep.iff_step_yield_or_tau
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {c c' : Config Op χ V m n} :
    (∃ i l', Config.IndexedStep c (i, l') c') ↔
    (∃ l', (l'.isYield ∨ l'.isSilent) ∧ Config.Step c l' c')
  := by
  constructor
  · simp only [forall_exists_index]
    intros _ _
    apply Config.IndexedStep.to_step_yield_or_tau
  · simp only [forall_exists_index]
    intros _ h
    apply Config.IndexedStep.from_step_yield_or_tau h.1 h.2

end Wavelet.Dataflow
