import Wavelet.Seq.Fn
import Wavelet.Dataflow.Proc
import Wavelet.Dataflow.AffineChan

import Wavelet.Determinacy.Defs
import Wavelet.Determinacy.Convert
import Wavelet.Determinacy.Determinism

/-! Definitions and lemmas about configurations having a disjoint set of tokens. -/

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

def asTok [PCM T] : V ⊕ T → T
  | .inl _ => PCM.zero
  | .inr t => t

def ChanMap.tokSum {χ : Type u} {V : Type v} {T : Type w}
  [PCM T] (map : ChanMap χ (V ⊕ T)) (name : χ) : T :=
  PCM.sum ((map name).map asTok)

def ChanMap.DisjointTokens
  [PCM T] (map : ChanMap χ (V ⊕ T)) : Prop :=
  -- Any finite subset of channels have valid token sum
  ∀ names : List χ, ✓ PCM.sum (names.map map.tokSum)

def ChanMap.DisjointWith
  [PCM T] (map : ChanMap χ (V ⊕ T)) (tok : T) : Prop :=
  -- Any finite subset of channels have valid token sum
  ∀ names : List χ, tok ⊥ PCM.sum (names.map map.tokSum)

@[simp]
def Config.DisjointTokens
  {Op : Type u} {V : Type v} {T : Type w}
  [Arity Op] [PCM T]
  (c : Config Op χ (V ⊕ T) m n) : Prop :=
  c.proc.HasNoTokenConst ∧
  c.chans.DisjointTokens

def InrDisjointTokens
  [PCM T]
  (v₁ v₂ : V ⊕ T) : Prop :=
  ∀ {t₁ t₂},
    v₁ = .inr t₁ →
    v₂ = .inr t₂ →
    t₁ ⊥ t₂

theorem mem_map_tok
  [PCM T] {map : ChanMap χ (V ⊕ T)}
  (h : .inr t₁ ∈ map n₁) : t₁ ∈ (map n₁).map asTok
  := by grind only [= List.mem_map, asTok, → List.eq_nil_of_map_eq_nil]

/-- Weaken `DisjointTokens` to a `Pairwise` statement. -/
def ChanMap.DisjointTokens.to_pairwise
  [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  (hdisj : map.DisjointTokens) :
    map.Pairwise InrDisjointTokens
  := by
  intros n₁ n₂ i j hne hi hj t₁ t₂ hget_i hget_j
  by_cases h : n₁ = n₂
  · subst h
    simp at hne
    have := hdisj [n₁]
    simp [ChanMap.tokSum] at this
    apply PCM.valid.le this
    have h₁ : t₁ = ((map n₁).map asTok)[i]'(by simp [hi]) := by simp [hget_i, asTok]
    have h₂ : t₂ = ((map n₁).map asTok)[j]'(by simp [hj]) := by simp [hget_j, asTok]
    rw [h₁, h₂]
    apply PCM.sum.le_disj_get hne
  · have := hdisj [n₁, n₂]
    simp [ChanMap.tokSum] at this
    apply PCM.valid.le this
    apply PCM.add.le_add_congr
    · apply PCM.sum.mem_to_le
      have := List.mem_of_getElem hget_i
      apply mem_map_tok this
    · apply PCM.sum.mem_to_le
      have := List.mem_of_getElem hget_j
      apply mem_map_tok this

def ChanMap.DisjointWith.imp_frame_preserving
  [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {tok₁ tok₂ : T}
  (hfp : tok₁ ⟹ tok₂)
  (hdisj_with : map.DisjointWith tok₁) :
    map.DisjointWith tok₂
  := by
  intros names
  have := hdisj_with names
  exact hfp _ this

def ChanMap.DisjointWith.imp_disj_toks
  [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)} {tok : T}
  (hdisj_with : map.DisjointWith tok) :
    map.DisjointTokens
  := by
  intros names
  have := hdisj_with names
  exact this.add_right

theorem empty_token_sum_zero
  [inst : PCM T] [PCM.Lawful T]
  (names : List χ) :
    PCM.sum (names.map (ChanMap.empty (χ := χ) (V := V ⊕ T)).tokSum) = inst.zero
  := by
  induction names with
  | nil => simp
  | cons _ _ ih => simp [ih, ChanMap.tokSum, ChanMap.empty]

theorem pop_vals_disj_toks
  [DecidableEq χ] [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {names : Vector χ n}
  {vals : Vector (V ⊕ T) n}
  (hdisj : map.DisjointTokens)
  (hpop : map.popVals names = some (vals, map')) :
    map'.DisjointWith (PCM.sum (vals.map asTok).toList)
  := sorry

theorem push_vals_disj_toks
  [DecidableEq χ] [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {names : Vector χ n} {vals : Vector (V ⊕ T) n}
  (hdisj : map.DisjointWith (PCM.sum (vals.map asTok).toList)) :
    (map.pushVals names vals).DisjointTokens
  := sorry

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

theorem async_op_interp_le_tok_sum
  [PCM T] [InterpConsts V]
  {aop : AsyncOp (V ⊕ T)}
  (hntok : aop.HasNoTokenConst)
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop') :
    PCM.sum (outputVals.map asTok) ≤ PCM.sum (inputVals.map asTok)
  := by
  sorry

@[simp]
theorem sum_as_tok_map_inl
  [PCM T] [PCM.Lawful T] {vals : List V} :
    PCM.sum (vals.map (asTok ∘ .inl) : List T) = PCM.zero
  := by
  induction vals with
  | nil => simp
  | cons _ _ ih => simp [asTok, ih]

@[simp]
theorem sum_as_tok_map_inr
  [PCM T] [PCM.Lawful T] {toks : List T} :
    PCM.sum (toks.map (asTok (V := V) ∘ .inr)) = PCM.sum toks
  := by
  induction toks with
  | nil => simp
  | cons _ _ ih => simp [asTok, ih]

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
    replace ⟨hntok, hdisj⟩ := hdisj
    rcases hstep with ⟨hguard, hstep⟩
    cases hguard with
    | spec_tau =>
      -- Async operators
      cases hstep with | step_async _ hget hinterp hpop =>
      simp
      have hdisj' := pop_vals_disj_toks hdisj hpop
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
      · apply push_vals_disj_toks
        apply ChanMap.DisjointWith.imp_frame_preserving _ hdisj'
        apply PCM.framePreserving.from_le
        simp [Vector.toList_map]
        exact async_op_interp_le_tok_sum hntok_aop hinterp
    | spec_yield =>
      -- Normal operators
      cases hstep with | step_op hmem hpop =>
      rename_i op inputVals outputVals chans' inputs outputs
      have hdisj' := pop_vals_disj_toks hdisj hpop
      constructor
      · exact hntok
      · apply push_vals_disj_toks
        apply ChanMap.DisjointWith.imp_frame_preserving _ hdisj'
        simp [Vector.toList_push, Vector.toList_map, asTok]
        apply hfp
    | spec_join houtputs₀ houtputs₁ hsum =>
      rename_i k l req rem inst toks vals outputVals
      -- Join
      cases hstep with | step_op hmem hpop =>
      rename_i chans' inputs outputs
      have hdisj' := pop_vals_disj_toks hdisj hpop
      simp [Vector.toList_map, Vector.toList_append] at hdisj'
      constructor
      · exact hntok
      · apply push_vals_disj_toks
        have houtput_vals : outputVals = #v[.inr (req vals), .inr rem] := by
          ext i hi
          match i with
          | 0 => simp [houtputs₀]
          | 1 => simp [houtputs₁]
        rw [houtput_vals]
        simp [asTok, hsum]
        exact hdisj'
    | spec_input => simp at hl
    | spec_output =>
      -- Output
      cases hstep with | step_output hpop =>
      have hdisj' := pop_vals_disj_toks hdisj hpop
      constructor
      · exact hntok
      · exact hdisj'.imp_disj_toks

/-- Stepping from an initial state with an input label results in a `DisjointTokens` state. -/
theorem Config.DisjointTokens.guarded_init_input
  [Arity Op] [PCM T] [PCM.Lawful T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : Dataflow.ConfigWithSpec opSpec χ m n}
  (hvalid : ioSpec.Valid)
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
  · apply push_vals_disj_toks
    simp [hinit]
    intros names
    simp [Vector.toList_push, Vector.toList_map, asTok,
      empty_token_sum_zero]
    simp [PCM.disjoint]
    apply hvalid.1

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
  [Arity Op] [PCM T] [PCM.Lawful T] [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : Dataflow.ConfigWithSpec opSpec χ m n × opInterp.S}
  (hvalid : ioSpec.Valid)
  (hntok : s.1.proc.HasNoTokenConst)
  (hinit : s.1.chans = ChanMap.empty)
  (hinput : (Config.InterpGuardStep opSpec ioSpec).Step s (.input vals) s') :
    s'.1.DisjointTokens
  := by
  cases hinput with | step_input hstep =>
  exact Config.DisjointTokens.guarded_init_input hvalid hntok hinit hstep

end Wavelet.Determinacy
