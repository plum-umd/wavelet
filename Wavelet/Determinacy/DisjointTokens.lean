import Wavelet.Seq.Fn
import Wavelet.Dataflow.Proc
import Wavelet.Determinacy.Defs

/-! Definitions and lemmas about configurations having a disjoint set of tokens. -/

namespace Wavelet.Determinacy

def InrDisjointTokens
  [PCM T]
  (v₁ v₂ : V ⊕ T) : Prop :=
  ∀ {t₁ t₂},
    v₁ = .inr t₁ →
    v₂ = .inr t₂ →
    t₁ ⊥ t₂

end Wavelet.Determinacy

namespace Wavelet.Seq

open Semantics Determinacy

def VarMap.Pairwise
  (P : V → V → Prop)
  (vars : VarMap χ V) : Prop :=
  ∀ {x₁ x₂ v₁ v₂},
    x₁ ≠ x₂ →
    vars.getVar x₁ = some v₁ →
    vars.getVar x₂ = some v₂ →
    P v₁ v₂

def VarMap.DisjointTokens [PCM T]
  (vars : VarMap χ (V ⊕ T)) : Prop :=
  vars.Pairwise InrDisjointTokens

@[simp]
theorem VarMap.pairwise_empty
  (P : V → V → Prop) :
  (VarMap.empty (χ := χ)).Pairwise P := by
  intros x₁ x₂ v₁ v₂ hne hget₁ hget₂
  simp [getVar, empty] at hget₁

@[simp]
def Config.DisjointTokens
  [Arity Op] [PCM T]
  (c : Config Op χ (V ⊕ T) m n) : Prop := c.vars.DisjointTokens

end Wavelet.Seq

namespace Wavelet.Dataflow

open Semantics Determinacy

/-- Defines a config property that imposes a
constraint on every pair of values in the config. -/
def Config.Pairwise
  [Arity Op]
  (P : V → V → Prop)
  (c : Config Op χ V m n) : Prop :=
  c.chans.Pairwise P

@[simp]
def Config.DisjointTokens
  [Arity Op] [PCM T]
  (c : Config Op χ (V ⊕ T) m n) : Prop :=
  c.Pairwise InrDisjointTokens

end Wavelet.Dataflow

namespace Wavelet.Determinacy

open Semantics Dataflow Seq

/--
`Config.DisjointTokens` is a state invariant of a guarded `Proc` semantics.

TODO: this requires the `opSpec` to be frame preserving.
-/
theorem proc_guard_inv_disj
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n) :
    (proc.semantics.guard (opSpec.Guard ioSpec)).IsInvariant
      Config.DisjointTokens
  := by
  apply Lts.IsInvariantAt.by_induction
  · simp [Dataflow.Config.init, Semantics.guard,
      Proc.semantics, Config.Pairwise]
  · intros s s' l hinv hstep
    sorry

/--
`Config.DisjointTokens` is a state invariant of a guarded `Fn` semantics.

TODO: not quite true. should disallow multiple inputs transitions
-/
theorem fn_guard_inv_disj
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (fn : FnWithSpec opSpec χ m n) :
    (fn.semantics.guard (opSpec.Guard ioSpec)).IsInvariant
      Config.DisjointTokens
  := by
  apply Lts.IsInvariantAt.by_induction
  · simp [Seq.Config.init, Semantics.guard,
      Fn.semantics, VarMap.DisjointTokens]
  · intros s s' l hinv hstep
    sorry

end Wavelet.Determinacy
