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
  | inv _ (some c) => c.isLeft
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
  ∀ names : List χ,
    names.Nodup → ✓ PCM.sum (names.map map.tokSum)

def ChanMap.DisjointWith
  [PCM T] (map : ChanMap χ (V ⊕ T)) (tok : T) : Prop :=
  -- Any finite subset of channels have valid token sum
  ∀ names : List χ,
    names.Nodup → tok ⊥ PCM.sum (names.map map.tokSum)

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
    apply PCM.valid.le (this h)
    apply PCM.add.le_add_congr
    · apply PCM.sum.mem_to_le
      have := List.mem_of_getElem hget_i
      apply mem_map_tok this
    · apply PCM.sum.mem_to_le
      have := List.mem_of_getElem hget_j
      apply mem_map_tok this

def ChanMap.DisjointTokens.to_disj_with_zero
  [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  (hdisj : map.DisjointTokens) :
    map.DisjointWith PCM.zero
  := by
  intros names
  have := hdisj names
  simp [PCM.disjoint]
  exact this

def ChanMap.DisjointWith.imp_frame_preserving
  [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {tok₁ tok₂ : T}
  (hfp : tok₁ ⟹ tok₂)
  (hdisj_with : map.DisjointWith tok₁) :
    map.DisjointWith tok₂
  := by
  intros names hnodup
  have := hdisj_with names hnodup
  exact hfp _ this

def ChanMap.DisjointWith.imp_le
  [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {tok₁ tok₂ : T}
  (hle : tok₂ ≤ tok₁)
  (hdisj_with : map.DisjointWith tok₁) :
    map.DisjointWith tok₂
  := hdisj_with.imp_frame_preserving (PCM.framePreserving.from_le hle)

def ChanMap.DisjointWith.to_disj_toks
  [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)} {tok : T}
  (hdisj_with : map.DisjointWith tok) :
    map.DisjointTokens
  := by
  intros names hnodup
  have := hdisj_with names hnodup
  exact this.add_right

theorem empty_token_sum_zero
  [inst : PCM T] [PCM.Lawful T]
  (names : List χ) :
    PCM.sum (names.map (ChanMap.empty (χ := χ) (V := V ⊕ T)).tokSum) = inst.zero
  := by
  induction names with
  | nil => simp
  | cons _ _ ih => simp [ih, ChanMap.tokSum, ChanMap.empty]

theorem pop_val_disj_with
  [DecidableEq χ] [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {name : χ} {val : V ⊕ T} {tok : T}
  (hdisj : map.DisjointWith tok)
  (hpop : map.popVal name = some (val, map')) :
    map'.DisjointWith (tok ⊔ asTok val)
  := by
  simp [ChanMap.popVal] at hpop
  split at hpop; contradiction
  rename_i val res heq
  simp at hpop
  have ⟨h₁, h₂⟩ := hpop
  subst h₁ h₂
  simp [ChanMap.DisjointWith]
  have hsimp_map {names} (hnmem : name ∉ names) :
    List.map (ChanMap.tokSum fun n => if n = name then res else map n) names
    = List.map (ChanMap.tokSum map) names
    := by
    apply List.map_congr_left
    intros n hn
    simp [ChanMap.tokSum]
    by_cases h : n = name
    · subst h
      exact False.elim (hnmem hn)
    · simp [h]
  intros names hnodup
  by_cases hmem : name ∈ names
  · have := hdisj names hnodup
    apply PCM.valid.le this
    rw [PCM.Lawful.add_assoc]
    apply PCM.add.le_add_congr
    · simp
    induction names with
    | nil => simp at hmem
    | cons name' names' ih =>
      by_cases h₁ : name = name'
      · subst h₁
        simp at hnodup ⊢
        rw [hsimp_map hnodup.1]
        simp [ChanMap.tokSum]
        rw [← @PCM.Lawful.add_assoc _ _ _ (asTok val)]
        have :
          asTok val ⊔ PCM.sum (List.map asTok res)
          = PCM.sum (List.map asTok (map name))
        := by simp [heq]
        simp [this]
      · simp [h₁] at hmem hnodup
        specialize ih hnodup.2 hmem
        simp
        rw [← PCM.Lawful.add_assoc]
        rw [@PCM.Lawful.add_comm _ _ _ (asTok val)]
        rw [PCM.Lawful.add_assoc]
        apply PCM.add.le_add_congr
        · simp [ChanMap.tokSum, Ne.symm h₁]
        · apply ih
          apply hdisj
          exact hnodup.2
  · rw [hsimp_map hmem]
    have := hdisj (name :: names) (by simp [hmem, hnodup])
    apply PCM.valid.le this
    rw [PCM.Lawful.add_assoc]
    apply PCM.add.le_add_congr
    · simp
    · simp
      apply PCM.add.le_add_congr
      · simp [ChanMap.tokSum, heq]
      · simp

theorem pop_vals_disj_with
  [DecidableEq χ] [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {names : Vector χ n}
  {vals : Vector (V ⊕ T) n}
  {tok : T}
  (hdisj : map.DisjointWith tok)
  (hpop : map.popVals names = some (vals, map')) :
    map'.DisjointWith (tok ⊔ PCM.sum (vals.map asTok).toList)
  := by
  induction names using Vector.back_induction
    generalizing map map' with
  | empty =>
    simp [Vector.eq_empty] at hpop ⊢
    subst hpop
    exact hdisj
  | push names' name ih =>
    simp [pop_vals_unfold, Option.bind] at hpop
    split at hpop; contradiction
    rename_i res' hpop'
    rcases res' with ⟨vals', map''⟩
    simp at hpop
    split at hpop; contradiction
    rename_i res hpop''
    rcases res with ⟨val, map'''⟩
    simp at hpop
    have hdisj' := ih hdisj hpop'
    have := pop_val_disj_with hdisj' hpop''
    simp [← hpop, Vector.toList_push]
    rw [← PCM.Lawful.add_assoc]
    exact this

theorem pop_vals_disj_toks
  [DecidableEq χ] [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {names : Vector χ n}
  {vals : Vector (V ⊕ T) n}
  (hdisj : map.DisjointTokens)
  (hpop : map.popVals names = some (vals, map')) :
    map'.DisjointWith (PCM.sum (vals.map asTok).toList)
  := by
  have := pop_vals_disj_with hdisj.to_disj_with_zero hpop
  simp at this
  exact this

theorem push_val_disj_with
  [DecidableEq χ] [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {name : χ} {val : V ⊕ T} {tok : T}
  (hdisj : map.DisjointWith (tok ⊔ asTok val)) :
    (map.pushVal name val).DisjointWith tok
  := by
  intros names hnodup
  have hsimp_map {names} (hnmem : name ∉ names) :
    List.map ((map.pushVal name val).tokSum) names
    = List.map (map.tokSum) names
    := by
    apply List.map_congr_left
    intros n hn
    simp [ChanMap.tokSum]
    by_cases h : n = name
    · subst h
      exact False.elim (hnmem hn)
    · simp [h, ChanMap.pushVal]
  by_cases hmem : name ∈ names
  · have hdisj' := hdisj names hnodup
    apply PCM.valid.le hdisj'
    rw [PCM.Lawful.add_assoc]
    apply PCM.add.le_add_congr
    · simp
    induction names generalizing tok with
    | nil => simp at hmem
    | cons name' names' ih =>
      simp at hmem
      by_cases h₁ : name = name'
      · subst h₁
        simp at hnodup ⊢
        rw [hsimp_map hnodup.1]
        simp [ChanMap.pushVal, ChanMap.tokSum]
        rw [← @PCM.Lawful.add_comm _ _ _ (asTok val)]
        rw [PCM.Lawful.add_assoc]
        rw [← PCM.Lawful.add_assoc]
        simp
      · simp [h₁] at hnodup hmem
        simp [ChanMap.pushVal, ChanMap.tokSum, Ne.symm h₁]
        rw [← PCM.Lawful.add_assoc]
        specialize ih hdisj hnodup.2 hmem
          (by
            apply PCM.valid.le hdisj'
            apply PCM.add.le_add_congr
            · simp
            · simp)
        apply PCM.le.trans
        · apply PCM.add.le_add_congr (PCM.le.refl _) ih
        · rw [← PCM.Lawful.add_assoc]
          rw [@PCM.Lawful.add_comm _ _ _ (asTok val)]
          simp
  · simp [hsimp_map hmem]
    have := hdisj names hnodup
    apply PCM.valid.le this
    apply PCM.add.le_add_congr
    · simp
    · simp

theorem push_vals_disj_with
  [DecidableEq χ] [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {names : Vector χ n} {vals : Vector (V ⊕ T) n} {tok : T}
  (hdisj : map.DisjointWith (tok ⊔ PCM.sum (vals.map asTok).toList)) :
    (map.pushVals names vals).DisjointWith tok
  := by
  induction names using Vector.back_induction
    generalizing map tok with
  | empty =>
    simp [Vector.eq_empty] at hdisj ⊢
    exact hdisj
  | push names' name' ih =>
    simp [push_vals_unfold]
    apply push_val_disj_with
    rw [← Vector.push_pop_back vals] at hdisj
    simp only [Vector.toList_map, Vector.toList_push] at hdisj
    simp at hdisj
    rw [@PCM.Lawful.add_comm _ _ _ _ (asTok vals.back)] at hdisj
    rw [← PCM.Lawful.add_assoc] at hdisj
    apply ih
    rw [Vector.toList_map]
    exact hdisj

theorem push_vals_disj_toks
  [DecidableEq χ] [PCM T] [PCM.Lawful T]
  {map : ChanMap χ (V ⊕ T)}
  {names : Vector χ n} {vals : Vector (V ⊕ T) n}
  (hdisj : map.DisjointWith (PCM.sum (vals.map asTok).toList)) :
    (map.pushVals names vals).DisjointTokens
  := by
  rw [← PCM.add.left_zero_id (a := PCM.sum (vals.map asTok).toList)] at hdisj
  have := push_vals_disj_with hdisj (names := names)
  exact this.to_disj_toks

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
  {s : ConfigWithSpec opSpec ioSpec χ}
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
  {s : ConfigWithSpec opSpec ioSpec χ}
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
  {s : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (haff : s.1.proc.AffineChan) :
    (Config.InterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s
  := by
  simp [Config.InterpGuardStep]
  have : (Config.InterpGuardStep opSpec ioSpec).IsInvariantAt _ _ :=
    (Lts.InterpStep.map_inv
      (lts' := opInterp.lts)
      (Inv := λ (s : ConfigWithSpec opSpec ioSpec χ) => s.proc.AffineChan)
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
  {s : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
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
    <;> try exact hntok
  rename V ⊕ T => val
  rename InterpConsts.isClonable _ = _ => h
  cases val <;> simp at h ⊢

theorem async_op_interp_le_tok_sum
  [PCM T] [PCM.Lawful T] [InterpConsts V]
  {aop : AsyncOp (V ⊕ T)}
  (hntok : aop.HasNoTokenConst)
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop') :
    PCM.sum (outputVals.map asTok) ≤ PCM.sum (inputVals.map asTok)
  := by
  cases hinterp with
  | interp_switch
  | interp_steer_true
  | interp_steer_false
  | interp_merge_left
  | interp_merge_right
  | interp_merge_decider
  | interp_forward
  | interp_sink => simp
  | interp_fork _ hclone =>
    rename V ⊕ T => val
    cases val <;> simp at hclone
    simp [asTok]
  | interp_order =>
    apply PCM.sum.mem_to_le
    simp only [List.map_singleton, PCM.sum.singleton]
    grind only [= List.mem_map, usr List.length_pos_of_mem, usr List.getElem_mem,
      → List.eq_nil_of_map_eq_nil]
  | interp_const =>
    rename_i c _ _ _
    cases c <;> simp [AsyncOp.HasNoTokenConst] at hntok
    simp [asTok]
  | interp_forwardc h₁ h₂ =>
    rename_i consts _
    simp only [AsyncOp.HasNoTokenConst] at hntok
    have : PCM.sum (List.map asTok consts.toList) = PCM.zero := by
      clear h₁ h₂
      induction consts using Vector.back_induction with
      | empty => simp
      | push xs x ih =>
        have := hntok x (by simp)
        cases x <;> simp at this
        simp [Vector.toList_push, asTok]
        apply ih
        intros x' hx'
        apply hntok
        simp [hx']
    simp
    simp [this]
  | interp_inv_init => simp
  | interp_inv_true =>
    rename V ⊕ T => val
    simp [AsyncOp.HasNoTokenConst] at hntok
    cases val <;> simp at hntok
    simp [asTok]
  | interp_inv_false => simp

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
  {s : Dataflow.ConfigWithSpec opSpec ioSpec χ}
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
      -- Normal operators with ghost tokens
      cases hstep with | step_op hmem hpop =>
      rename_i op ghost inputVals outputVals hpre chans' inputs outputs
      have hdisj' := pop_vals_disj_toks hdisj hpop
      constructor
      · exact hntok
      · apply push_vals_disj_toks
        apply ChanMap.DisjointWith.imp_frame_preserving _ hdisj'
        cases ghost with
        | true =>
          simp [Vector.toList_push, Vector.toList_map, asTok, WithSpec.opInputs]
          apply hfp
        | false =>
          simp at hpre
          simp [Vector.toList_push, Vector.toList_map, asTok, WithSpec.opInputs]
          simp [← hpre]
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
      · exact hdisj'.to_disj_toks

/-- Stepping from an initial state with an input label results in a `DisjointTokens` state. -/
theorem Config.DisjointTokens.guarded_init_input
  [Arity Op] [PCM T] [PCM.Lawful T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : Dataflow.ConfigWithSpec opSpec ioSpec χ}
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
    intros names _
    simp [Vector.toList_append, Vector.toList_map,
      empty_token_sum_zero, PCM.disjoint]
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
  {s : Dataflow.ConfigWithSpec opSpec ioSpec χ × opInterp.S}
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
  {s : Dataflow.ConfigWithSpec opSpec ioSpec χ × opInterp.S}
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
  {s s' : Dataflow.ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hvalid : ioSpec.Valid)
  (hntok : s.1.proc.HasNoTokenConst)
  (hinit : s.1.chans = ChanMap.empty)
  (hinput : (Config.InterpGuardStep opSpec ioSpec).Step s (.input vals) s') :
    s'.1.DisjointTokens
  := by
  cases hinput with | step_input hstep =>
  exact Config.DisjointTokens.guarded_init_input hvalid hntok hinit hstep

end Wavelet.Determinacy
