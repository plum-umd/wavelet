import Wavelet.Dataflow.Proc
import Wavelet.Dataflow.AffineChan

import Wavelet.Thm.Semantics.Simulation

/-!
Definitions for a generic framework to prove that a local graph rewrite
(replacing the atoms at indices `I` with new atoms `P'`) is a forward simulation.

A rewrite rule only needs to provide a `LocalSimRel`, which relates the states
of the matched atoms and the replacement atoms (and the channels), and is
preserved by steps of the matched atoms and by steps of the rest of the graph
(`frame_pop` and `frame_push`). See `Wavelet.Thm.Compile.Rewrite.Sim` for the
main theorems.
-/

namespace Wavelet.Dataflow

open Semantics

/-- All input names of a list of atoms. -/
def AtomicProcs.inputNames [Arity Op] (aps : AtomicProcs Op χ V) : List χ :=
  aps.flatMap (·.inputs)

/-- All output names of a list of atoms. -/
def AtomicProcs.outputNames [Arity Op] (aps : AtomicProcs Op χ V) : List χ :=
  aps.flatMap (·.outputs)

/-- All channel names used in a process. -/
def Proc.allNames [Arity Op] (proc : Proc Op χ V m n) : List χ :=
  proc.inputs.toList ++ proc.outputs.toList ++
  proc.atoms.inputNames ++ proc.atoms.outputNames

/-- Values pushed (or popped) to/from channel `y` when pushing `vals` to `names` in order.
Used to describe channel updates point-wise. -/
def ChanMap.pushed [DecidableEq χ] (names : List χ) (vals : List V) (y : χ) : List V :=
  (names.zip vals).filterMap (λ (x, v) => if x = y then some v else none)

/-- Two atoms that only differ in the internal states of merges or invariants. -/
inductive AtomicProc.SameShape [Arity Op] : AtomicProc Op χ V → AtomicProc Op χ V → Prop
  | refl : SameShape ap ap
  | merge [NeZero n] :
    SameShape (.async (.merge st n) ins outs) (.async (.merge st' n) ins outs)
  | inv :
    SameShape (.async (.inv flavor c) ins outs) (.async (.inv flavor c') ins outs)

/-- Values in the outputs of a constant (possibly through one fork)
are always the same as the constant. -/
def ConstInv [Arity Op] (proc : Proc Op χ V m n) (chans : ChanMap χ V) : Prop :=
  ∀ v k inputs outputs, .async (.const v k) inputs outputs ∈ proc.atoms →
    ∀ o ∈ outputs,
      (∀ w ∈ chans o, w = v) ∧
      ∀ k' outputs', .async (.fork k') [o] outputs' ∈ proc.atoms →
        ∀ o' ∈ outputs', ∀ w ∈ chans o', w = v

/-- If a push touches an output of a fork, then it is exactly
that fork firing on a clonable value. -/
def ForkPush [Arity Op] [InterpConsts V]
  (proc : Proc Op χ V m n) (outs : List χ) (vals : List V) : Prop :=
  ∀ x ∈ outs, ∀ k inputs outputs, .async (.fork k) inputs outputs ∈ proc.atoms → x ∈ outputs →
    outs = outputs ∧ ∃ v, InterpConsts.isClonable v ∧ ∀ w ∈ vals, w = v

/-- A configuration with only the given atoms and no inputs/outputs. -/
def LocalConfig [Arity Op]
  (aps : AtomicProcs Op χ V) (chans : ChanMap χ V) : Config Op χ V 0 0 :=
  { proc := { inputs := #v[], outputs := #v[], atoms := aps }, chans }

/-- Zero or more τ steps of the given atoms alone. -/
def LocalTauStar [Arity Op] [DecidableEq χ] [InterpConsts V]
  (aps : AtomicProcs Op χ V) (chans : ChanMap χ V)
  (aps' : AtomicProcs Op χ V) (chans' : ChanMap χ V) : Prop :=
  (Config.Step (Op := Op) (χ := χ) (V := V) (m := 0) (n := 0)).TauStar .τ
    (LocalConfig aps chans) (LocalConfig aps' chans')

end Wavelet.Dataflow

namespace Wavelet.Compile

open Semantics Dataflow

/-- Elements at the given indices, in the order of `I`. -/
def matchedOf (aps : List α) (I : List Nat) : List α := I.filterMap (aps[·]?)

/-- Elements not at the given indices, in the original order (same as in `Rewrite.apply`). -/
def unmatchedOf (aps : List α) (I : List Nat) : List α :=
  aps.mapIdx (·, ·) |>.filter (λ (i, _) => i ∉ I) |>.map (·.snd)

/-- Conditions on names for replacing the atoms at `I` with `P'`: every name in `P'`
is either used in the same way (as an input or an output) by the matched atoms,
or is fresh. -/
structure RewriteNames [Arity Op]
  (proc : Proc Op χ V m n) (I : List Nat) (P' : AtomicProcs Op χ V) : Prop where
  idx_nodup : I.Nodup
  idx_lt : ∀ i ∈ I, i < proc.atoms.length
  inputs_nodup : P'.inputNames.Nodup
  outputs_nodup : P'.outputNames.Nodup
  inputs_sub : ∀ x ∈ P'.inputNames,
    x ∈ AtomicProcs.inputNames (matchedOf proc.atoms I) ∨ x ∉ proc.allNames
  outputs_sub : ∀ x ∈ P'.outputNames,
    x ∈ AtomicProcs.outputNames (matchedOf proc.atoms I) ∨ x ∉ proc.allNames

/--
A local simulation for replacing the atoms at `I` with `P'`.

`R L₀ chans₀ L₁ chans₁` relates the current states of the matched atoms (`L₀`, in the
order of `I`) and the channels of the original process to the current states of the
replacement atoms (`L₁`) and the channels of the rewritten process.

Channel updates are stated point-wise using `ChanMap.pushed`, e.g., popping `inputVals`
from `inputs` in `chans` results in `chans'` iff `∀ y, chans y = pushed inputs inputVals y ++ chans' y`.
-/
structure LocalSimRel [Arity Op] [DecidableEq χ] [InterpConsts V]
  (proc : Proc Op χ V m n) (I : List Nat) (P' : AtomicProcs Op χ V)
  (R : AtomicProcs Op χ V → ChanMap χ V → AtomicProcs Op χ V → ChanMap χ V → Prop) : Prop where
  init : R (matchedOf proc.atoms I) .empty P' .empty
  /-- Popping a channel read by neither the matched nor the replacement atoms
  (i.e., read by the rest of the graph or the environment). -/
  frame_pop : ∀ {L₀ chans₀ L₁ chans₁ x v} {chans₀' : ChanMap χ V},
    x ∉ AtomicProcs.inputNames (matchedOf proc.atoms I) → x ∉ P'.inputNames →
    R L₀ chans₀ L₁ chans₁ →
    (∀ y, chans₀ y = (if y = x then [v] else []) ++ chans₀' y) →
    ∃ chans₁',
      (∀ y, chans₁ y = (if y = x then [v] else []) ++ chans₁' y) ∧
      R L₀ chans₀' L₁ chans₁'
  /-- Pushing to channels written by neither the matched nor the replacement atoms. -/
  frame_push : ∀ {L₀ chans₀ L₁ chans₁} {outs : List χ} {vals : List V},
    outs.length = vals.length →
    (∀ x ∈ outs, x ∉ AtomicProcs.outputNames (matchedOf proc.atoms I) ∧ x ∉ P'.outputNames) →
    outs.Nodup →
    ForkPush proc outs vals →
    R L₀ chans₀ L₁ chans₁ →
    R L₀ (λ y => chans₀ y ++ ChanMap.pushed outs vals y)
      L₁ (λ y => chans₁ y ++ ChanMap.pushed outs vals y)
  /-- A matched operator fires: some replacement operator fires with the same label. -/
  step_op : ∀ {L₀ chans₀ L₁ chans₁ op}
    {inputs : Vector χ (Arity.ι op)} {outputs : Vector χ (Arity.ω op)}
    {inputVals : Vector V (Arity.ι op)} {outputVals : Vector V (Arity.ω op)}
    {chans₀' : ChanMap χ V},
    ConstInv proc chans₀ →
    List.Forall₂ AtomicProc.SameShape (matchedOf proc.atoms I) L₀ →
    R L₀ chans₀ L₁ chans₁ →
    .op op inputs outputs ∈ L₀ →
    (∀ y, chans₀ y = ChanMap.pushed inputs.toList inputVals.toList y ++ chans₀' y) →
    ∃ (inputs' : Vector χ (Arity.ι op)) (outputs' : Vector χ (Arity.ω op)) (chans₁' : ChanMap χ V),
      .op op inputs' outputs' ∈ L₁ ∧
      (∀ y, chans₁ y = ChanMap.pushed inputs'.toList inputVals.toList y ++ chans₁' y) ∧
      R L₀ (λ y => chans₀' y ++ ChanMap.pushed outputs.toList outputVals.toList y)
        L₁ (λ y => chans₁' y ++ ChanMap.pushed outputs'.toList outputVals.toList y)
  /-- A matched async operator fires: the replacement atoms take zero or more τ steps. -/
  step_async : ∀ {L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs}
    {inputs outputs : List χ} {inputVals outputVals : List V} {chans₀' : ChanMap χ V},
    ConstInv proc chans₀ →
    List.Forall₂ AtomicProc.SameShape (matchedOf proc.atoms I) L₀ →
    R L₀ chans₀ L₁ chans₁ →
    L₀[i]? = some (.async aop allInputs allOutputs) →
    aop.Interp (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop' →
    inputs.length = inputVals.length →
    outputs.length = outputVals.length →
    (∀ y, chans₀ y = ChanMap.pushed inputs inputVals y ++ chans₀' y) →
    ∃ L₁' chans₁',
      LocalTauStar L₁ chans₁ L₁' chans₁' ∧
      R (L₀.set i (.async aop' allInputs allOutputs))
        (λ y => chans₀' y ++ ChanMap.pushed outputs outputVals y) L₁' chans₁'

/-- The relation only relates the initial states to the initial states. -/
def PreservesInitRel [Arity Op]
  (proc : Proc Op χ V m n) (I : List Nat) (P' : AtomicProcs Op χ V)
  (R : AtomicProcs Op χ V → ChanMap χ V → AtomicProcs Op χ V → ChanMap χ V → Prop) : Prop :=
  ∀ {L₁ chans₁}, R (matchedOf proc.atoms I) .empty L₁ chans₁ → L₁ = P' ∧ chans₁ = .empty

/-- Replacing the atoms at `I` with `P'` is a forward simulation preserving initial states. -/
def RuleOK [Arity Op] [DecidableEq χ] [InterpConsts V]
  (proc : Proc Op χ V m n) (I : List Nat) (P' : AtomicProcs Op χ V) : Prop :=
  RewriteNames proc I P' ∧ ∃ R, LocalSimRel proc I P' R ∧ PreservesInitRel proc I P' R

/-- Replacing the atoms at `I` with `P'` is a forward simulation. -/
def RuleOKNoInit [Arity Op] [DecidableEq χ] [InterpConsts V]
  (proc : Proc Op χ V m n) (I : List Nat) (P' : AtomicProcs Op χ V) : Prop :=
  RewriteNames proc I P' ∧ ∃ R, LocalSimRel proc I P' R

end Wavelet.Compile
