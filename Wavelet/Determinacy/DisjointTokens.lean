import Wavelet.Seq.Fn
import Wavelet.Dataflow.Proc
import Wavelet.Dataflow.AffineChan

import Wavelet.Determinacy.Defs
import Wavelet.Determinacy.Convert
import Wavelet.Determinacy.Determinism

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

open Semantics Dataflow

theorem proc_guarded_inv_aff
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec χ m n}
  (haff : s.proc.AffineChan) :
    (Config.GuardStep opSpec ioSpec).IsInvariantAt (·.proc.AffineChan) s
  := by
  simp [Config.GuardStep]
  have : (Config.GuardStep opSpec ioSpec).IsInvariantAt _ _ :=
    (Lts.GuardStep.map_inv (P := opSpec.Guard ioSpec) (haff.inv))
  intros s' tr hsteps
  exact this hsteps

theorem proc_indexed_guarded_inv_aff
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec χ m n}
  (haff : s.proc.AffineChan) :
    (Config.IdxGuardStep opSpec ioSpec).IsInvariantAt (·.proc.AffineChan) s
  := by
  have : (Config.GuardStep opSpec ioSpec).IsInvariantAt _ _ := proc_guarded_inv_aff haff
  have : (Config.IdxGuardStep opSpec ioSpec).IsInvariantAt _ _ := this.map_step (λ hstep => by
    simp [Lts.Step] at hstep
    exact ⟨_, hstep.to_guarded⟩)
  intros s' tr hsteps
  exact this hsteps

theorem proc_interp_guarded_inv_aff
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec χ m n × opInterp.S}
  (haff : s.1.proc.AffineChan) :
    (Config.InterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s
  := by
  simp [Config.InterpGuardStep]
  have : (Config.InterpGuardStep opSpec ioSpec).IsInvariantAt _ _ :=
    (Lts.InterpStep.map_inv
      (lts' := opInterp.lts)
      (Inv := λ (s : ConfigWithSpec opSpec χ m n) => s.proc.AffineChan)
      (Lts.GuardStep.map_inv (P := opSpec.Guard ioSpec) (haff.inv)))
  intros s' tr hsteps
  exact this hsteps

theorem proc_indexed_interp_guarded_inv_aff
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec χ m n × opInterp.S}
  (haff : s.1.proc.AffineChan) :
    (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s
  := by
  have : (Config.InterpGuardStep opSpec ioSpec).IsInvariantAt _ _ := proc_interp_guarded_inv_aff haff
  have : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt _ _ := this.map_step (λ hstep => by
    simp [Lts.Step] at hstep
    exact ⟨_, hstep.to_interp_guarded⟩)
  intros s' tr hsteps
  exact this hsteps

/--
`Config.DisjointTokens` is an invariant of a guarded `Proc` semantics,
when restricted to non-input labels.
-/
theorem Config.DisjointTokens.guarded_inv
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : Dataflow.ConfigWithSpec opSpec χ m n}
  (haff : s.proc.AffineChan)
  (hdisj : s.DisjointTokens) :
    (Config.GuardStep opSpec ioSpec).IsInvariantForAt
      (¬ ·.isInput)
      Config.DisjointTokens s
  := by
  sorry

/--
`Config.DisjointTokens` is an invariant of an interpreted and guarded `Proc` semantics.
-/
theorem Config.DisjointTokens.interp_guarded_inv
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : Dataflow.ConfigWithSpec opSpec χ m n × opInterp.S}
  (haff : s.1.proc.AffineChan)
  (hdisj : s.1.DisjointTokens) :
    (Config.InterpGuardStep opSpec ioSpec).IsInvariantForAt
      (¬ ·.isInput)
      (Config.DisjointTokens ·.1) s
  := by
  intros s' tr hsteps htr
  suffices h :
    s'.fst.proc.AffineChan ∧
    s'.fst.DisjointTokens by
    with_reducible
    exact h.2
  induction hsteps with
  | refl => exact ⟨haff, hdisj⟩
  | tail pref tail ih =>
    rename_i s tr₁ s₁ l₂ s₂
    simp at htr
    have ⟨haff', hdisj'⟩ := ih haff hdisj
      (by
        intros l hmem
        simp [htr (.inl hmem)])
    have hinv_aff : (Config.GuardStep opSpec ioSpec).IsInvariantAt _ _ :=
      proc_guarded_inv_aff haff'
    have hinv_disj : (Config.GuardStep opSpec ioSpec).IsInvariantForAt _ _ _ :=
      Config.DisjointTokens.guarded_inv haff' hdisj'
    simp [Config.InterpGuardStep] at tail
    cases tail with
    | step_tau tail
    | step_output tail
    | step_yield tail =>
      exact ⟨
        (hinv_aff.unfold tail).1,
        (hinv_disj.unfold tail (by simp)).1,
      ⟩
    | step_input =>
      have := htr (.inr rfl)
      simp at this

/--
Converts the previous invariant results to `Config.IdxInterpGuardStep`
-/
theorem Config.DisjointTokens.indexed_interp_guarded_inv
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : Dataflow.ConfigWithSpec opSpec χ m n × opInterp.S}
  (haff : s.1.proc.AffineChan)
  (hdisj : s.1.DisjointTokens) :
    (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt
      (Config.DisjointTokens ·.1) s
  := by
  with_reducible
  have : (Config.InterpGuardStep opSpec ioSpec).IsInvariantForAt _ _ _ :=
    Config.DisjointTokens.interp_guarded_inv haff hdisj
  have := this.imp_labels
    (Labels₂ := λ (l : Label _ V m n) => l.isSilent)
    (by intros l; cases l <;> simp)
  have : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantForAt _ _ _ :=
    this.map_step
      (Labels₂ := λ _ => True)
      (by
        intros c c' l hl hstep
        have hstep' := Config.IdxInterpGuardStep.to_interp_guarded hstep
        have := proc_indexed_interp_guarded_step_label hstep
        simp [this] at hstep'
        exact ⟨_, by simp, hstep'⟩)
  exact Lts.IsInvariantForAt.to_inv_at (by simp) this

end Wavelet.Determinacy
