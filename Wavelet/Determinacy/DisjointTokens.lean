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

/-- The async op does not generate ghost token constants. -/
def AsyncOp.HasNoTokenConst :
  AsyncOp (V ⊕ T) → Prop
  | const c _ => c.isLeft
  | forwardc _ _ consts => ∀ v ∈ consts, v.isLeft
  | _ => True

def AtomicProc.HasNoTokenConst [Arity Op] :
  AtomicProc Op χ (V ⊕ T) → Prop
  | .op _ _ _ => True
  | .async aop _ _ => aop.HasNoTokenConst

@[simp]
def AtomicProcs.HasNoTokenConst
  [Arity Op] (aps : AtomicProcs Op χ (V ⊕ T)) : Prop
  := ∀ ap ∈ aps, ap.HasNoTokenConst

@[simp]
def Proc.HasNoTokenConst
  [Arity Op] (proc : Proc Op χ (V ⊕ T) m n) : Prop
  := proc.atoms.HasNoTokenConst

/-- Defines a config property that imposes a
constraint on every pair of values in the config. -/
@[simp]
def Config.Pairwise
  [Arity Op]
  (P : V → V → Prop)
  (c : Config Op χ V m n) : Prop :=
  c.chans.Pairwise P

@[simp]
def Config.DisjointTokens
  [Arity Op] [PCM T]
  (c : Config Op χ (V ⊕ T) m n) : Prop :=
  c.proc.HasNoTokenConst ∧
  c.Pairwise InrDisjointTokens

end Wavelet.Dataflow

namespace Wavelet.Determinacy

open Semantics Dataflow

@[simp]
theorem InrDisjointTokens.pairwise_map_inl
  [PCM T] {vals : Vector V n} :
    List.Pairwise (InrDisjointTokens (T := T)) (Vector.map .inl vals).toList
  := by
  apply List.pairwise_of_forall_mem_list
  intros x hx y hy
  simp at hx hy
  replace ⟨_, _, hx⟩ := hx
  replace ⟨_, _, hy⟩ := hy
  subst hx hy
  simp [InrDisjointTokens]

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

theorem async_op_interp_preserves_no_token_const
  [InterpConsts V]
  {aop : AsyncOp (V ⊕ T)}
  (hntok : aop.HasNoTokenConst)
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop') :
    aop'.HasNoTokenConst
  := by
  cases hinterp
    <;> simp [AsyncOp.HasNoTokenConst] at hntok ⊢
    <;> exact hntok

theorem async_op_interp_preserves_pairwise_disj_tokens
  [PCM T] [InterpConsts V]
  {aop : AsyncOp (V ⊕ T)}
  (hntok : aop.HasNoTokenConst)
  (hpw_inputs : inputVals.Pairwise InrDisjointTokens)
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop') :
    outputVals.Pairwise InrDisjointTokens
  := by
  sorry

theorem async_op_interp_preserves_frame_preserving
  [PCM T] [InterpConsts V]
  {aop : AsyncOp (V ⊕ T)}
  (hntok : aop.HasNoTokenConst)
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop') :
    ∀ t₂ v₂,
      v₂ ∈ outputVals → v₂ = .inr t₂ →
      ∃ t₁ v₁, v₁ ∈ inputVals ∧ v₁ = .inr t₁ ∧ t₁ ⟹ t₂
  := by
  sorry

theorem pairwise_with_vals_frame_preserving
  [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {vals₁ : Vector (V ⊕ T) n}
  {vals₂ : Vector (V ⊕ T) m}
  (hpw_vals₁ : map.PairwiseWithVals InrDisjointTokens vals₁)
  (hfp : ∀ t₂ v₂,
    v₂ ∈ vals₂ → v₂ = .inr t₂ →
    ∃ t₁ v₁, v₁ ∈ vals₁ ∧ v₁ = .inr t₁ ∧ t₁ ⟹ t₂) :
    map.PairwiseWithVals InrDisjointTokens vals₂
  := by
  intros name v₁ v₂ hmem₁ hmem₂
  cases v₂ with
  | inl => simp [InrDisjointTokens]
  | inr t₂ =>
    have ⟨t₁', v₁', hmem₁', hv₁', hfp'⟩ := hfp t₂ (.inr t₂) hmem₂ rfl
    simp [InrDisjointTokens]
    intros t₁ hv₁
    have := hpw_vals₁ hmem₁ hmem₁' hv₁ hv₁'
    have := hfp' _ this.symm
    exact PCM.disjoint.symm this

theorem pairwise_disj_push_tok
  [PCM T]
  {vals : Vector V n}
  {tok : T} :
    List.Pairwise InrDisjointTokens
      ((vals.map .inl).push (.inr tok)).toList
  := by
  sorry

/--
`Config.DisjointTokens` is an invariant of a guarded `Proc` semantics,
when restricted to non-input labels.
-/
theorem Config.DisjointTokens.guarded_inv
  [Arity Op] [PCM T] [PCM.Lawful T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (hfp : opSpec.FramePreserving)
  {s : Dataflow.ConfigWithSpec opSpec χ m n}
  (haff : s.proc.AffineChan)
  (hdisj : s.DisjointTokens) :
    (Config.GuardStep opSpec ioSpec).IsInvariantForAt
      (¬ ·.isInput)
      Config.DisjointTokens s
  := by
  apply Lts.IsInvariantForAt.by_strong_induction
  · exact hdisj
  · intros s₁ s₂ l tr hpref htr hdisj hl hstep
    have haff' := proc_guarded_inv_aff haff hpref
    simp at haff'
    simp [Config.GuardStep] at hstep
    simp at hdisj
    have ⟨hntok, hpw⟩ := hdisj
    rcases hstep with ⟨hguard, hstep⟩
    cases hguard with
    | spec_tau =>
      -- Async operators
      cases hstep with | step_async _ hget hinterp hpop =>
      simp
      have ⟨hpw', hpw_vals, hpw_chans'_vals⟩ := pop_vals_pairwise hpw hpop
      have hntok_aop := hntok _ (List.mem_of_getElem hget)
      constructor
      · intros ap hmem
        have := List.mem_or_eq_of_mem_set hmem
        cases this with
        | inl hmem => exact hntok _ hmem
        | inr heq =>
          subst heq
          simp [AtomicProc.HasNoTokenConst]
          exact async_op_interp_preserves_no_token_const hntok_aop hinterp
      · apply push_vals_pairwise hpw'
        · exact async_op_interp_preserves_pairwise_disj_tokens
            hntok_aop hpw_vals hinterp
        · have hfp := async_op_interp_preserves_frame_preserving
            hntok_aop hinterp
          apply pairwise_with_vals_frame_preserving
          · exact hpw_chans'_vals
          · simp only [Vector.mem_toList_iff] at hfp
            exact hfp
    | spec_yield =>
      -- Normal operators
      cases hstep with | step_op hmem hpop =>
      rename_i op inputVals outputVals chans' inputs outputs
      have ⟨hpw', hpw_vals, hpw_chans'_vals⟩ := pop_vals_pairwise hpw hpop
      constructor
      · exact hntok
      · apply push_vals_pairwise hpw'
        · exact pairwise_disj_push_tok
        · apply pairwise_with_vals_frame_preserving
          · exact hpw_chans'_vals
          · intros t₂ v₂ hmem₂ hv₂
            simp at hmem₂
            cases hmem₂ with
            | inl h => simp [hv₂] at h
            | inr h =>
              simp [h] at hv₂
              subst hv₂
              exists opSpec.pre op inputVals
              exists .inr (opSpec.pre op inputVals)
              simp
              apply hfp
    | spec_join houtputs₀ houtputs₁ hsum hdisj =>
      rename_i k l req rem inst toks vals outputVals
      -- Join
      cases hstep with | step_op hmem hpop =>
      rename_i chans' inputs outputs
      have ⟨hpw', hpw_vals, hpw_chans'_vals⟩ := pop_vals_pairwise hpw hpop
      constructor
      · exact hntok
      · have houtput_vals : outputVals = #v[.inr (req vals), .inr rem] := by
          ext i hi
          match i with
          | 0 => simp [houtputs₀]
          | 1 => simp [houtputs₁]
        apply push_vals_pairwise hpw'
        · rw [houtput_vals]
          simp [InrDisjointTokens]
          exact hdisj
        · rw [houtput_vals]

          sorry
    | spec_input => simp at hl
    | spec_output =>
      -- Output
      cases hstep with | step_output =>
      sorry

/-- Stepping from an initial state with an input label results in a `DisjointTokens` state. -/
theorem Config.DisjointTokens.guarded_init_input
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : Dataflow.ConfigWithSpec opSpec χ m n}
  (hntok : s.proc.HasNoTokenConst)
  (hinit : s.chans = ChanMap.empty)
  (hinput : (Config.GuardStep opSpec ioSpec).Step s (.input vals) s') :
    s'.DisjointTokens
  := by
  cases hinput with | step hguard hstep =>
  cases hguard
  cases hstep with | step_init =>
  simp
  constructor
  · exact hntok
  · apply push_vals_pairwise
    · simp [hinit]
    · simp [Vector.toList_push]
      apply List.pairwise_append.mpr
      simp [InrDisjointTokens]
    · simp [hinit, ChanMap.empty]

/--
`Config.DisjointTokens` is an invariant of an interpreted and guarded `Proc` semantics.
-/
theorem Config.DisjointTokens.interp_guarded_inv
  [Arity Op] [PCM T] [PCM.Lawful T] [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (hfp : opSpec.FramePreserving)
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
      Config.DisjointTokens.guarded_inv hfp haff' hdisj'
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
  [Arity Op] [PCM T] [PCM.Lawful T] [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (hfp : opSpec.FramePreserving)
  {s : Dataflow.ConfigWithSpec opSpec χ m n × opInterp.S}
  (haff : s.1.proc.AffineChan)
  (hdisj : s.1.DisjointTokens) :
    (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt
      (Config.DisjointTokens ·.1) s
  := by
  with_reducible
  have : (Config.InterpGuardStep opSpec ioSpec).IsInvariantForAt _ _ _ :=
    Config.DisjointTokens.interp_guarded_inv hfp haff hdisj
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

theorem Config.DisjointTokens.interp_guarded_init_input
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : Dataflow.ConfigWithSpec opSpec χ m n × opInterp.S}
  (hntok : s.1.proc.HasNoTokenConst)
  (hinit : s.1.chans = ChanMap.empty)
  (hinput : (Config.InterpGuardStep opSpec ioSpec).Step s (.input vals) s') :
    s'.1.DisjointTokens
  := by
  cases hinput with | step_input hstep =>
  exact Config.DisjointTokens.guarded_init_input hntok hinit hstep

end Wavelet.Determinacy
