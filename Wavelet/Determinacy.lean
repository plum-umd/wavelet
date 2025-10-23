import Mathlib.Control.ULiftable
import Mathlib.Logic.Basic

import Wavelet.Semantics
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

namespace Wavelet.Semantics

def InrDisjointTokens
  [PCM T]
  (v₁ v₂ : V ⊕ T) : Prop :=
  ∀ {t₁ t₂},
    v₁ = .inr t₁ →
    v₂ = .inr t₂ →
    t₁ ⊥ t₂

def EqModGhost : V ⊕ T → V ⊕ T → Prop
  | .inl v₁, .inl v₂ => v₁ = v₂
  | .inr _, .inr _ => True
  | _, _ => False

instance : IsRefl (V ⊕ T) EqModGhost where
  refl v := by cases v <;> simp [EqModGhost]

/-- Map permission tokens in the spec through a PCM map. -/
def OpSpec.mapTokens
  [Arity Op]
  (opSpec : OpSpec Op V T₁)
  (hom : T₁ → T₂) : OpSpec Op V T₂ := {
    pre op inputs := hom (opSpec.pre op inputs),
    post op inputs outputs := hom (opSpec.post op inputs outputs),
  }

def IOSpec.mapTokens
  (ioSpec : IOSpec V T₁ m n)
  (hom : T₁ → T₂) : IOSpec V T₂ m n := {
    pre vals := hom (ioSpec.pre vals),
    post vals := hom (ioSpec.post vals),
  }

end Wavelet.Semantics

namespace Wavelet.Seq

open Semantics

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

abbrev ExprWithSpec
  [Arity Op] (opSpec : Semantics.OpSpec Op V T) χ m n
  := Expr (WithSpec Op opSpec) χ (m + 1) (n + 1)

abbrev FnWithSpec
  [Arity Op] (opSpec : Semantics.OpSpec Op V T) χ m n
  := Fn (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

end Wavelet.Seq

namespace Wavelet.Dataflow

open Semantics

def ChanMap.Pairwise
  (P : V → V → Prop)
  (map : ChanMap χ V) : Prop :=
  ∀ {x₁ x₂}
    {buf₁ buf₂ : List V}
    {i : Fin buf₁.length}
    {j : Fin buf₂.length},
    x₁ ≠ x₂ ∨ i.val ≠ j.val →
    map x₁ = some buf₁ →
    map x₂ = some buf₂ →
    P buf₁[i] buf₂[j]

@[simp]
theorem ChanMap.pairwise_empty
  (P : V → V → Prop) :
  (ChanMap.empty (χ := χ)).Pairwise P := by
  intros x₁ x₂ buf₁ buf₂ i j hne hget₁ hget₂
  simp [ChanMap.empty] at hget₁
  simp [hget₁] at i
  exact Fin.elim0 i

/-- Checks if two channel maps are equal modulo an equivalence relation on values. -/
def ChanMap.EqMod
  (Eq : V → V → Prop)
  (map₁ map₂ : ChanMap χ V) : Prop :=
  ∀ {name : χ}, List.Forall₂ Eq (map₁ name) (map₂ name)

instance {Eq : V → V → Prop} [IsRefl V Eq] : IsRefl (ChanMap χ V) (ChanMap.EqMod Eq) where
  refl map := by
    intros name
    apply List.forall₂_refl

@[simp]
theorem ChanMap.EqMod.eq_eq {map₁ map₂ : ChanMap χ V} :
    ChanMap.EqMod Eq map₁ map₂ ↔ map₁ = map₂
  := by
  constructor
  · simp [EqMod]
    intros h
    funext
    apply h
  · intros h
    simp [h, EqMod]

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

/-- Equal configurations modulo a equivalence relation on values. -/
def Config.EqMod
  [Arity Op] (Eq : V → V → Prop)
  (c₁ c₂ : Config Op χ V m n) : Prop :=
  c₁.proc = c₂.proc ∧
  ChanMap.EqMod Eq c₁.chans c₂.chans

instance {Eq : V → V → Prop} [Arity Op] [IsRefl V Eq] :
  IsRefl (Config Op χ V m n) (Config.EqMod Eq) where
  refl c := by
    constructor
    · rfl
    · apply IsRefl.refl

@[simp]
theorem Config.EqMod.eq_eq
  [Arity Op] {c₁ c₂ : Config Op χ V m n} :
    Config.EqMod Eq c₁ c₂ ↔ c₁ = c₂
  := by
  simp [EqMod]
  cases c₁; cases c₂
  simp

abbrev ProcWithSpec
  [Arity Op] (opSpec : Semantics.OpSpec Op V T) χ m n
  := Proc (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

def AsyncOp.mapValues
  (f : V₁ → V₂) : AsyncOp V₁ → AsyncOp V₂
  | .switch n => .switch n
  | .steer flavor n => .steer flavor n
  | .carry state n => .carry state n
  | .merge n => .merge n
  | .forward n => .forward n
  | .fork n => .fork n
  | .const c n => .const (f c) n
  | .forwardc n m consts => .forwardc n m (consts.map f)
  | .sink n => .sink n

def AtomicProc.mapTokens
  [Arity Op]
  {opSpec : OpSpec Op V T₁}
  (hom : T₁ → T₂) :
  AtomicProc (WithSpec Op opSpec) χ (V ⊕ T₁) → AtomicProc (WithSpec Op (opSpec.mapTokens hom)) χ (V ⊕ T₂)
  | .op (.op o) inputs outputs => .op (.op o) inputs outputs
  | .op (.join k l req) inputs outputs => .op (.join k l (hom ∘ req)) inputs outputs
  | .async o inputs outputs =>
    .async (o.mapValues mapValue) inputs outputs
  where
    mapValue : V ⊕ T₁ → V ⊕ T₂
      | .inl v => .inl v
      | .inr t => .inr (hom t)

def AtomicProcs.mapTokens
  [Arity Op]
  {opSpec : OpSpec Op V T₁}
  (hom : T₁ → T₂)
  (aps : AtomicProcs (WithSpec Op opSpec) χ (V ⊕ T₁)) :
    AtomicProcs (WithSpec Op (opSpec.mapTokens hom)) χ (V ⊕ T₂)
  := aps.map (.mapTokens hom)

/-- Map the tokens through a PCM map. Note that on a well-formed
process, this should not change anything, since we should not have
token constants in the processes. -/
def Proc.mapTokens
  [Arity Op]
  {opSpec : OpSpec Op V T₁}
  (hom : T₁ → T₂)
  (proc : ProcWithSpec opSpec χ m n) :
    ProcWithSpec (OpSpec.mapTokens opSpec hom) χ m n
  := {
    inputs := proc.inputs,
    outputs := proc.outputs,
    atoms := proc.atoms.mapTokens hom,
  }

end Wavelet.Dataflow

namespace Wavelet.Compile

open Semantics Seq Dataflow

-- /-- Erase ghost tokens. -/
-- def eraseGhost
--   [Arity Op] [PCM T]
--   {opSpec : Semantics.OpSpec Op V T}
--   (proc : ProcWithSpec opSpec χ m n) : Proc Op χ V m n
--   := sorry

-- /-- Backward simulation for `eraseGhost`. -/
-- theorem sim_erase_ghost
--   [Arity Op] [PCM T]
--   [InterpConsts V]
--   [DecidableEq χ]
--   [DecidableEq χ']
--   {opSpec : Semantics.OpSpec Op V T}
--   {ioSpec : IOSpec V T m n}
--   (proc : ProcWithSpec opSpec χ m n) :
--   (eraseGhost proc).semantics ≲ᵣ
--     proc.semantics.guard (opSpec.Guard ioSpec)
--   := sorry

-- /-- Forward simulation for liveness. -/
-- theorem sim_erase_ghost_forward
--   [Arity Op] [PCM T]
--   [InterpConsts V]
--   [DecidableEq χ]
--   [DecidableEq χ']
--   {opSpec : Semantics.OpSpec Op V T}
--   {ioSpec : IOSpec V T m n}
--   (proc : ProcWithSpec opSpec χ m n) :
--   proc.semantics.guard (opSpec.Guard ioSpec)
--     ≲ᵣ (eraseGhost proc).semantics
--   := sorry

/-- A constraint on two yield labels that if their
operator and inputs match, the outputs should match. -/
def Label.Deterministic
  [Arity Op]
  {V : Type v} {m n}
  (l₁ l₂ : Label Op V m n) : Prop :=
    ∀ {op inputVals outputVals₁ outputVals₂},
      l₁ = .yield op inputVals outputVals₁ →
      l₂ = .yield op inputVals outputVals₂ →
      outputVals₁ = outputVals₂

/-- A constraint on two yield labels that if their
operator and inputs match, the outputs should match. -/
def Label.DeterministicMod
  [Arity Op]
  {V : Type v} {m n}
  (EqV : V → V → Prop)
  (l₁ l₂ : Label Op V m n) : Prop :=
    ∀ {op inputVals outputVals₁ outputVals₂},
      l₁ = .yield op inputVals outputVals₁ →
      l₂ = .yield op inputVals outputVals₂ →
      List.Forall₂ EqV outputVals₁.toList outputVals₂.toList

@[simp]
theorem Label.DeterministicMod.eq_eq
  [Arity Op] {l₁ l₂ : Label Op V m n} :
    Label.DeterministicMod Eq l₁ l₂ ↔ Label.Deterministic l₁ l₂
  := by
  constructor
  · intros h
    simp [Label.Deterministic]
    simp [Label.DeterministicMod] at h
    intros _ _ _ _ h₁ h₂
    apply Vector.toList_inj.mp
    apply h h₁ h₂
  · intros h
    simp [Label.DeterministicMod]
    simp [Label.Deterministic] at h
    intros _ _ _ _ h₁ h₂
    apply Vector.toList_inj.mpr
    apply h h₁ h₂

/-- If two labels are either yield or silent and are deterministic (mod `EqV`). -/
def Label.IsYieldOrSilentAndDetMod
  [Arity Op] (EqV : V → V → Prop)
  (l₁ : Label Op V m n) (l₂ : Label Op V m n) : Prop :=
  (l₁.isYield ∨ l₁.isSilent) ∧
  (l₂.isYield ∨ l₂.isSilent) ∧
  Label.DeterministicMod EqV l₁ l₂

def Label.IsYieldOrSilentAndDet
  [Arity Op]
  (l₁ : Label Op V m n) (l₂ : Label Op V m n) : Prop :=
  (l₁.isYield ∨ l₁.isSilent) ∧
  (l₂.isYield ∨ l₂.isSilent) ∧
  Label.Deterministic l₁ l₂

@[simp]
theorem Label.IsYieldOrSilentAndDetMod.eq_eq
  [Arity Op] {l₁ l₂ : Label Op V m n} :
    Label.IsYieldOrSilentAndDetMod Eq l₁ l₂ ↔ Label.IsYieldOrSilentAndDet l₁ l₂
  := by
  simp only [Label.IsYieldOrSilentAndDetMod, Label.IsYieldOrSilentAndDet]
  simp

def Label.EqMod
  [Arity Op]
  (Eq : V → V → Prop)
  (l₁ l₂ : Label Op V m n) : Prop :=
  match l₁, l₂ with
  | .input vals₁, .input vals₂ =>
      List.Forall₂ Eq vals₁.toList vals₂.toList
  | .output vals₁, .output vals₂ =>
      List.Forall₂ Eq vals₁.toList vals₂.toList
  | .yield op₁ inputs₁ outputs₁, .yield op₂ inputs₂ outputs₂ =>
      op₁ = op₂ ∧
      List.Forall₂ Eq inputs₁.toList inputs₂.toList ∧
      List.Forall₂ Eq outputs₁.toList outputs₂.toList
  | .τ, .τ => True
  | _, _ => False

instance {Eq : V → V → Prop} [Arity Op] [IsRefl V Eq] :
  IsRefl (Label Op V m n) (Label.EqMod Eq) where
  refl l := by cases l <;> simp [Label.EqMod, IsRefl.refl]

@[simp]
def Label.EqMod.eq_eq
  [Arity Op] {l₁ l₂ : Label Op V m n} :
    Label.EqMod Eq l₁ l₂ ↔ l₁ = l₂
  := by
  constructor
  · cases l₁ <;> cases l₂
    any_goals simp [Label.EqMod]
    · intros h₁ h₂ h₃
      subst h₁
      simp [Vector.toList_inj] at h₂
      simp [Vector.toList_inj] at h₃
      simp [h₂, h₃]
    · simp [Vector.toList_inj]
    · simp [Vector.toList_inj]
  · intros h
    simp [h, IsRefl.refl]

theorem chan_map_push_vals_equiv
  [DecidableEq χ]
  {map : ChanMap χ V}
  {vals₁ vals₂ : Vector V k}
  {Eq : V → V → Prop}
  (hequiv : List.Forall₂ Eq vals₁.toList vals₂.toList) :
    ChanMap.EqMod EqV
      (ChanMap.pushVals names vals₁ map)
      (ChanMap.pushVals names vals₂ map)
  := sorry

/-- A PCM homomorphism induces a simulation. -/
theorem sim_map_tokens
  [Arity Op] [PCM T₁] [PCM T₂]
  [InterpConsts V]
  [DecidableEq χ]
  [DecidableEq χ']
  {opSpec : Semantics.OpSpec Op V T₁}
  {ioSpec : IOSpec V T₁ m n}
  (hom : T₁ → T₂) [PCM.Hom hom]
  (proc : ProcWithSpec opSpec χ m n) :
    proc.semantics.guard (opSpec.Guard ioSpec)
      ≲ᵣ (proc.mapTokens hom).semantics.guard
        ((opSpec.mapTokens hom).Guard (ioSpec.mapTokens hom))
  := sorry

/--
Without considering shared operator states, and when restricted
to silent/yield labels, a well-formed `Proc` has a strongly
confluent (and thus confluent) semantics, modulo a given
equivalence relation on values to capture certain non-determinism
in the operator semantics.
-/
theorem proc_strong_confl_at_mod
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  (EqV : V → V → Prop)
  [hrefl : IsRefl V EqV]
  (proc : Proc Op χ V m n)
  (s : proc.semantics.S)
  (haff : s.proc.AffineChan) :
    proc.semantics.lts.StronglyConfluentAtMod
      (Label.IsYieldOrSilentAndDetMod EqV)
      (Config.EqMod EqV)
      (Label.EqMod EqV)
      s
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  have ⟨hlabel₁, hlabel₂, hyield_det⟩ := hcompat
  have ⟨_, _, ⟨haff_nodup, haff_disj⟩, _⟩ := haff
  by_cases heq : l₁ = l₂ ∧ s₁' = s₂'
  · left
    simp [heq]
    constructor
    · apply IsRefl.refl
    · simp [Proc.semantics] at s₂'
      apply IsRefl.refl
  · simp at heq
    -- Keep some acronyms so that they don't get expanded
    generalize hs₁' : s₁' = s₁''
    generalize hs₂' : s₂' = s₂''
    cases hstep₁ <;> cases hstep₂
    any_goals
      simp at hlabel₁ hlabel₂
    -- Commute two `step_op`s
    case neg.step_op.step_op =>
      rename_i
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hmem₁ hpop₁
        op₂ inputs₂ outputs₂ inputVals₂ outputVals₂ chans₂' hmem₂ hpop₂
      have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem₁
      have ⟨j, hj, hget_j⟩ := List.getElem_of_mem hmem₂
      by_cases h : i = j
      · left
        subst h
        simp [hget_i] at hget_j
        have ⟨h₁, h₂, h₃⟩ := hget_j
        subst h₁; subst h₂; subst h₃
        simp [hpop₁] at hpop₂
        have ⟨h₄, h₅⟩ := hpop₂
        subst h₄; subst h₅
        have heq_outputs := hyield_det (by rfl) (by rfl)
        simp only [← hs₁', ← hs₂']
        constructor
        · constructor
          · rfl
          · constructor
            · apply List.forall₂_refl
            · exact heq_outputs
        · constructor
          · rfl
          · simp
            exact chan_map_push_vals_equiv heq_outputs
      · right
        have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj ⟨i, hi⟩ ⟨j, hj⟩ (by simp [h])
        simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
        have hstep₁' : proc.semantics.lts.Step s₁'' _ _ :=
          .step_op
            (outputVals := outputVals₂)
            (by simp [← hs₁']; exact hmem₂)
            (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
        have hstep₂' : proc.semantics.lts.Step s₂'' _ _ :=
          .step_op (outputVals := outputVals₁)
            (by simp [← hs₂']; exact hmem₁)
            (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
        rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
        simp only [← hs₁'] at hstep₁' ⊢
        simp only [← hs₂'] at hstep₂' ⊢
        exact ⟨_, _, hstep₁', hstep₂', by simp [IsRefl.refl]⟩
    -- Commute `step_op` and `step_async`
    case neg.step_op.step_async =>
      right
      rename_i
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hmem₁ hpop₁
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' j hinterp₂ hj hget_j hpop₂
      have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem₁
      have hne : i ≠ j := by
        intro heq; subst heq
        simp [hget_i] at hget_j
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
        ⟨i, hi⟩ ⟨j, hj⟩
        (by simp [hne])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      replace hdisj_inputs := List.disjoint_of_subset_right
        (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs
      replace hdisj_outputs := List.disjoint_of_subset_right
        (async_op_interp_output_sublist hinterp₂).subset hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      -- simp [happ₂] at hmem₁
      have hstep₁' : proc.semantics.lts.Step s₁'' _ _ :=
        .step_async (i := j)
          (by simp [← hs₁']; exact hj)
          (by simp [← hs₁']; exact hget_j)
          hinterp₂
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₂' : proc.semantics.lts.Step s₂'' _ _ :=
        .step_op (outputVals := outputVals₁)
          (by
            simp [← hs₂']
            apply List.mem_set_ne
            exact hget_i
            exact hne.symm)
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
      simp only [← hs₁'] at hstep₁' ⊢
      simp only [← hs₂'] at hstep₂' ⊢
      exact ⟨_, _, hstep₁', hstep₂', by simp [IsRefl.refl]⟩
    -- Commute `step_async` and `step_op`
    case neg.step_async.step_op =>
      right
      rename_i
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' j hinterp₂ hj hget_j hpop₂
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hmem₁ hpop₁
      have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem₁
      have hne : i ≠ j := by
        intro heq; subst heq
        simp [hget_i] at hget_j
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
        ⟨i, hi⟩ ⟨j, hj⟩
        (by simp [hne])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      replace hdisj_inputs := List.disjoint_of_subset_right
        (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs
      replace hdisj_outputs := List.disjoint_of_subset_right
        (async_op_interp_output_sublist hinterp₂).subset hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      -- simp [happ₂] at hmem₁
      have hstep₂' : proc.semantics.lts.Step s₂'' _ _ :=
        .step_async (i := j)
          (by simp [← hs₂']; exact hj)
          (by simp [← hs₂']; exact hget_j)
          hinterp₂
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₁' : proc.semantics.lts.Step s₁'' _ _ :=
        .step_op (outputVals := outputVals₁)
          (by
            simp [← hs₁']
            apply List.mem_set_ne
            exact hget_i
            exact hne.symm)
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₂'
      simp only [← hs₁'] at hstep₁' ⊢
      simp only [← hs₂'] at hstep₂' ⊢
      exact ⟨_, _, hstep₁', hstep₂', by simp [IsRefl.refl]⟩
    -- Commute two `step_async`s
    case neg.step_async.step_async =>
      right
      rename_i
        _ _ aop₁ aop₁' allInputs₁ allOutputs₁
        inputs₁ inputVals₁ outputs₁ outputVals₁ chans₁' i hinterp₁ hi hget_i hpop₁
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' j hinterp₂ hj hget_j hpop₂
      by_cases h : i = j
      -- Firing the same async op => final state should be the same
      · apply False.elim
        simp at heq
        apply heq
        subst h
        simp [hget_i] at hget_j
        have ⟨h₁, h₂, h₃⟩ := hget_j
        subst h₁; subst h₂; subst h₃
        simp at hinterp₁ hinterp₂
        have heq_inputs_len := async_op_interp_det_inputs_len hinterp₁ hinterp₂
        simp at heq_inputs_len
        subst heq_inputs_len
        have heq_inputs : inputs₁ = inputs₂ := by
          -- Generealize so that we can do case analysis
          generalize hinputs₁ : inputs₁.toList = inputs₁
          generalize hinput_vals₁ : inputVals₁.toList = inputVals₁
          generalize houtputs₁ : outputs₁.toList = outputs₁
          generalize houtput_vals₁ : outputVals₁.toList = outputVals₁
          rw [hinputs₁, hinput_vals₁, houtputs₁, houtput_vals₁] at hinterp₁
          generalize hinputs₂ : inputs₂.toList = inputs₂
          generalize hinput_vals₂ : inputVals₂.toList = inputVals₂
          generalize houtputs₂ : outputs₂.toList = outputs₂
          generalize houtput_vals₂ : outputVals₂.toList = outputVals₂
          rw [hinputs₂, hinput_vals₂, houtputs₂, houtput_vals₂] at hinterp₂
          cases hinterp₁ <;> cases hinterp₂
          any_goals
            simp [← hinputs₁, Vector.toList_inj] at hinputs₂
            simp [hinputs₂]
          -- Merges are slightly complicated,
          -- since the inputs can depend on input decider value...
          -- TODO: a better solution would be to add local states
          -- to merge similar to carry.
          case
            interp_merge_true.interp_merge_false |
            interp_merge_false.interp_merge_true =>
            have := pop_vals_eq_head hinputs₁ hinputs₂ hpop₁ hpop₂
            simp [hinput_vals₁, hinput_vals₂] at this
            subst this
            grind only
        have heq_input_vals : inputVals₁ = inputVals₂ := by
          simp [heq_inputs] at hpop₁
          simp [hpop₁] at hpop₂
          simp [hpop₂]
        have heq_outputs := async_op_interp_det_outputs hinterp₁ hinterp₂
          (by simp [heq_inputs])
          (by simp [heq_input_vals])
        have heq_chans : chans₁' = chans₂' := by
          simp [heq_inputs] at hpop₁
          simp [hpop₁] at hpop₂
          simp [hpop₂]
        congr 1
        · congr
          simp [heq_outputs]
        · have ⟨h, _⟩ := Vector.toList_inj_heq heq_outputs.1
          subst h
          simp [Vector.toList_inj] at heq_outputs
          simp [heq_outputs, heq_chans]
      -- Firing two different async ops
      · have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
          ⟨i, hi⟩ ⟨j, hj⟩
          (by simp [h])
        simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        replace hdisj_inputs := List.disjoint_of_subset_left
          (async_op_interp_input_sublist hinterp₁).subset hdisj_inputs
        replace hdisj_inputs := List.disjoint_of_subset_right
          (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs
        replace hdisj_outputs := List.disjoint_of_subset_left
          (async_op_interp_output_sublist hinterp₁).subset hdisj_outputs
        replace hdisj_outputs := List.disjoint_of_subset_right
          (async_op_interp_output_sublist hinterp₂).subset hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
        have hstep₁' : proc.semantics.lts.Step s₁'' _ _ :=
          .step_async (i := j)
            (by simp [← hs₁', hj])
            (by simp [← hs₁', h]; exact hget_j)
            hinterp₂
            (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
        have hstep₂' : proc.semantics.lts.Step s₂'' _ _ :=
          .step_async (i := i)
            (by simp [← hs₂', hi])
            (by simp [← hs₂', Ne.symm h]; exact hget_i)
            hinterp₁
            (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
        rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
        simp only [← hs₁'] at hstep₁' ⊢
        simp only [← hs₂'] at hstep₂' ⊢
        exact ⟨_, _, hstep₁',
          (by
            apply Lts.Step.eq_rhs hstep₂'
            rfl),
          (by
            rw [List.set_comm]
            · simp [IsRefl.refl]
            · exact h)
        ⟩

theorem proc_strong_confl_at
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  (proc : Proc Op χ V m n)
  (s : proc.semantics.S)
  (haff : s.proc.AffineChan) :
    proc.semantics.lts.StronglyConfluentAt
      Label.IsYieldOrSilentAndDet
      s
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  have ⟨hcompat₁, hcompat₂, hcompat₃⟩ := hcompat
  have := proc_strong_confl_at_mod Eq proc s haff hstep₁ hstep₂
    (by simp [hcompat])
  simp at this
  exact this

/-- Similar to `guard_strong_confl_at` but for `StronglyConfluentAtMod`. -/
theorem guard_strong_confl_at_mod
  [Arity Op] [Arity Op']
  (sem : Semantics Op V m n)
  (s : sem.S)
  {Guard : Label Op V m n → Label Op' V' m' n' → Prop}
  {EqS : sem.S → sem.S → Prop}
  {EqL : Label Op V m n → Label Op V m n → Prop}
  {EqL' : Label Op' V' m' n' → Label Op' V' m' n' → Prop}
  {Compat : Label Op V m n → Label Op V m n → Prop}
  (hguard_congr : ∀ {l₁ l₂ l₁' l₂'}, Guard l₁ l₁' → Guard l₂ l₂' → EqL l₁ l₂ → EqL' l₁' l₂')
  (hconfl : sem.lts.StronglyConfluentAtMod Compat EqS EqL s) :
    (sem.guard Guard).lts.StronglyConfluentAtMod
      (λ l₁' l₂' => ∀ {l₁ l₂},
        Guard l₁ l₁' →
        Guard l₂ l₂' →
        Compat l₁ l₂)
      EqS EqL' s
  := by
  intros s₁' s₂' l₁' l₂' hstep₁ hstep₂ hcompat
  rcases hstep₁ with ⟨hguard₁', hstep₁⟩
  rcases hstep₂ with ⟨hguard₂', hstep₂⟩
  have hcompat' := hcompat hguard₁' hguard₂'
  cases hconfl hstep₁ hstep₂ hcompat' with
  | inl heq =>
    left
    simp [heq.2, hguard_congr hguard₁' hguard₂' heq.1]
  | inr h =>
    right
    have ⟨s₁'', s₂'', hstep₁', hstep₂', heq⟩ := h
    exists s₁'', s₂''
    and_intros
    · exact ⟨hguard₂', hstep₁'⟩
    · exact ⟨hguard₁', hstep₂'⟩
    · exact heq

theorem guard_strong_confl_at
  [Arity Op] [Arity Op']
  (sem : Semantics Op V m n)
  (s : sem.S)
  {Guard : Label Op V m n → Label Op' V' m' n' → Prop}
  {Compat : Label Op V m n → Label Op V m n → Prop}
  (hguard_congr : ∀ {l₁ l₂ l₁' l₂'}, Guard l₁ l₁' → Guard l₂ l₂' → l₁ = l₂ → l₁' = l₂')
  (hconfl : sem.lts.StronglyConfluentAt Compat s) :
    (sem.guard Guard).lts.StronglyConfluentAt
      (λ l₁' l₂' => ∀ {l₁ l₂},
        Guard l₁ l₁' →
        Guard l₂ l₂' →
        Compat l₁ l₂)
      s
  := by
  intros s₁' s₂' l₁' l₂' hstep₁ hstep₂ hcompat
  rcases hstep₁ with ⟨hguard₁', hstep₁⟩
  rcases hstep₂ with ⟨hguard₂', hstep₂⟩
  have hcompat' := hcompat hguard₁' hguard₂'
  cases hconfl hstep₁ hstep₂ hcompat' with
  | inl heq =>
    left
    simp [heq.2, hguard_congr hguard₁' hguard₂' heq.1]
  | inr h =>
    right
    have ⟨s', hstep₁', hstep₂'⟩ := h
    exists s'
    constructor
    · exact ⟨hguard₂', hstep₁'⟩
    · exact ⟨hguard₁', hstep₂'⟩

theorem op_spec_guard_eq_congr
  [Arity Op] [PCM T]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {l₁ l₂ : Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)}
  {l₁' l₂' : Label Op V m n}
  (hguard₁ : opSpec.Guard ioSpec l₁ l₁')
  (hguard₂ : opSpec.Guard ioSpec l₂ l₂')
  (heq : l₁ = l₂) : l₁' = l₂' := by
  subst heq
  cases l₁ with
  | yield op inputs outputs =>
    cases op with
    | op op =>
      cases hguard₁
      rename_i inputs₁ outputs₁
      generalize hinputs₁' :
        (Vector.map Sum.inl inputs₁).push (Sum.inr (opSpec.pre op inputs₁)) = inputs₁'
      generalize houtputs₁' :
        (Vector.map Sum.inl outputs₁).push (Sum.inr (opSpec.post op inputs₁ outputs₁)) = outputs₁'
      rw [hinputs₁', houtputs₁'] at hguard₂
      cases hguard₂
      rename_i inputs₂ outputs₂
      simp [Vector.push_eq_push] at hinputs₁' houtputs₁'
      have heq₁ := Vector.inj_map (by simp [Function.Injective]) hinputs₁'.2
      have heq₂ := Vector.inj_map (by simp [Function.Injective]) houtputs₁'.2
      simp [heq₁, heq₂]
    | join k l req =>
      cases hguard₁ with | spec_join h₁ h₂ =>
      rename_i rem₁ toks₁ vals₁
      generalize h :
        (Vector.map Sum.inr rem₁ : Vector (V ⊕ T) _) ++
          (Vector.map Sum.inl toks₁ : Vector (V ⊕ T) _) = x
      rw [h] at hguard₂
      cases hguard₂
      rfl
  | input vals =>
    cases hguard₁ with | spec_input =>
    rename_i vals₁
    generalize h :
      (Vector.map Sum.inl vals₁).push (Sum.inr (ioSpec.pre vals₁)) = x
    rw [h] at hguard₂
    cases hguard₂
    simp [Vector.push_eq_push] at h
    have heq := Vector.inj_map (by simp [Function.Injective]) h.2
    simp [heq]
  | output vals =>
    cases hguard₁ with | spec_output =>
    rename_i vals₁
    generalize h :
      (Vector.map Sum.inl vals₁).push (Sum.inr (ioSpec.post vals₁)) = x
    rw [h] at hguard₂
    cases hguard₂
    simp [Vector.push_eq_push] at h
    have heq := Vector.inj_map (by simp [Function.Injective]) h.2
    simp [heq]
  | τ =>
    cases hguard₁
    cases hguard₂
    rfl

theorem forall₂_push_toList_to_forall₂
  {α β}
  {xs : Vector α n}
  {ys : Vector β n}
  {x : α} {y : β}
  {R : α → β → Prop}
  (hforall₂ : List.Forall₂ R (xs.push x).toList (ys.push y).toList) :
    List.Forall₂ R xs.toList ys.toList ∧ R x y := by
  sorry

theorem forall₂_to_forall₂_push_toList
  {α β}
  {xs : Vector α n}
  {ys : Vector β n}
  {x : α} {y : β}
  {R : α → β → Prop}
  (hforall₂ : List.Forall₂ R xs.toList ys.toList)
  (hxy : R x y) :
    List.Forall₂ R (xs.push x).toList (ys.push y).toList := by
  sorry

/-- Similar to `theorem op_spec_guard_eq_congr` but for `OpSpec.TrivGuard`. -/
theorem op_spec_triv_guard_eq_congr
  [Arity Op]
  {opSpec : OpSpec Op V T}
  {l₁ l₂ : Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)}
  {l₁' l₂' : Label Op V m n}
  (hguard₁ : opSpec.TrivGuard l₁ l₁')
  (hguard₂ : opSpec.TrivGuard l₂ l₂')
  (heq : Label.EqMod EqModGhost l₁ l₂) : l₁' = l₂' := by
  cases l₁ <;> cases l₂
    <;> cases hguard₁
    <;> cases hguard₂
    <;> simp [Label.EqMod] at heq
  any_goals rfl
  case yield.yield.triv_yield.triv_yield =>
    have ⟨h₁, heq₂, heq₃⟩ := heq
    subst h₁
    replace ⟨heq₂, _⟩ := forall₂_push_toList_to_forall₂ heq₂
    replace ⟨heq₃, _⟩ := forall₂_push_toList_to_forall₂ heq₃
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq₂
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq₃
    simp [heq₂, heq₃]
  case input.input.triv_input.triv_input =>
    replace ⟨heq, _⟩ := forall₂_push_toList_to_forall₂ heq
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq
    simp [heq]
  case output.output.triv_output.triv_output =>
    replace ⟨heq, _⟩ := forall₂_push_toList_to_forall₂ heq
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq
    simp [heq]

/-- If the label pair generated by a guarded semantics
satisfies `Label.IsYieldOrSilentAndDet`, then the original
unchecked label must satisfy `Label.IsYieldOrSilentAndDet EqModGhost` -/
theorem guard_label_compat_inversion
  [Arity Op] [PCM T] [PCM.Cancellative T]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {l₁' l₂' : Label Op V m n}
  {l₁ l₂ : Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)}
  (hcompat : Label.IsYieldOrSilentAndDet l₁' l₂')
  (hguard₁ : opSpec.Guard ioSpec l₁ l₁')
  (hguard₂ : opSpec.Guard ioSpec l₂ l₂') :
    Label.IsYieldOrSilentAndDet l₁ l₂
  := by
  simp [Label.IsYieldOrSilentAndDet, Label.Deterministic]
  cases hguard₁ <;> cases hguard₂ <;> simp
  any_goals
    simp [Label.IsYieldOrSilentAndDet] at hcompat
  case spec_join.spec_join =>
    rename_i
      k₁ l₁ req₁ rem₁ toks₁ vals₁ outputs₁ houtputs₁₀ houtputs₁₁ hsum₁
      k₂ l₂ req₂ rem₂ toks₂ vals₂ outputs₂ houtputs₂₀ houtputs₂₁ hsum₂
    intros op inputs outputs₁' outputs₂' hop₁ hinputs₁' houtputs₁' hop₂ hinputs₂' houtputs₂'
    cases op <;> simp at hop₁
    have ⟨h₁, h₂, h₃⟩ := hop₁
    subst h₁; subst h₂; subst h₃
    simp at hop₂
    have ⟨h₁, h₂, h₃⟩ := hop₂
    subst h₁; subst h₂; subst h₃
    simp at hinputs₁'
    simp [← hinputs₁'] at hinputs₂'
    have ⟨h₁, h₂⟩ := Vector.append_inj hinputs₂'
    replace h₁ := Vector.inj_map (by simp [Function.Injective]) h₁
    replace h₂ := Vector.inj_map (by simp [Function.Injective]) h₂
    subst h₁; subst h₂
    have heq_rem : rem₁ = rem₂ := by
      simp [← hsum₂] at hsum₁
      exact PCM.Cancellative.cancel_left hsum₁
    subst heq_rem
    simp at houtputs₁' houtputs₂'
    simp [← houtputs₁', ← houtputs₂']
    apply Vector.ext
    intros i hi
    match h : i with
    | 0 => simp [houtputs₁₀, houtputs₂₀]
    | 1 => simp [houtputs₁₁, houtputs₂₁]
  case spec_yield.spec_yield =>
    rename_i
      op₁ inputs₁ outputs₁
      op₂ inputs₂ outputs₂
    intros op inputs outputs₁' outputs₂'
      hop₁ hinputs₁' houtputs₁'
      hop₂ hinputs₂' houtputs₂'
    cases op <;> simp at hop₁
    subst hop₁
    simp at hop₂
    subst hop₂
    simp only [heq_eq_eq] at *
    simp [← hinputs₁', Vector.push_eq_push] at hinputs₂'
    have heq_inputs := Vector.inj_map (by simp [Function.Injective]) hinputs₂'.2
    subst heq_inputs
    simp [← houtputs₁', ← houtputs₂', Vector.push_eq_push]
    simp [Label.Deterministic] at hcompat
    have heq_outputs : outputs₁ = outputs₂ := by
      apply hcompat
      any_goals rfl
    simp [heq_outputs]
  all_goals
    intros op
    cases op <;> simp

/-- Similar to `guard_label_compat_inversion` but for `OpSpec.TrivGuard`. -/
theorem guard_label_triv_compat_inversion
  [Arity Op]
  {opSpec : OpSpec Op V T}
  {l₁' l₂' : Label Op V m n}
  {l₁ l₂ : Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)}
  (hcompat : Label.IsYieldOrSilentAndDet l₁' l₂')
  (hguard₁ : opSpec.TrivGuard l₁ l₁')
  (hguard₂ : opSpec.TrivGuard l₂ l₂') :
    Label.IsYieldOrSilentAndDetMod EqModGhost l₁ l₂
  := by
  cases l₁ <;> cases l₂
    <;> cases hguard₁
    <;> cases hguard₂
    <;> simp [Label.IsYieldOrSilentAndDet, Label.Deterministic] at hcompat
    <;> simp [Label.IsYieldOrSilentAndDetMod, Label.DeterministicMod]
  any_goals
    intros op
    cases op <;> simp
  case yield.yield.triv_yield.triv_yield.op =>
    rename_i
      op₁ inputs₁ outputs₁ tok₁₁ tok₁₂
      op₂ inputs₂ outputs₂ tok₂₁ tok₂₂ _
    intros inputs' outputs₁' outputs₂'
      hop₁ hinputs₁' houtputs₁'
      hop₂ hinputs₂' houtputs₂'
    subst hop₁; subst hop₂
    have heq_inputs : inputs₁ = inputs₂ := by
      simp at hinputs₁' hinputs₂'
      simp [← hinputs₁', Vector.push_eq_push] at hinputs₂'
      have heq_inputs := Vector.inj_map (by simp [Function.Injective]) hinputs₂'.2
      simp [heq_inputs]
    subst heq_inputs
    have heq_outputs : outputs₁ = outputs₂ := by
      apply hcompat
      any_goals rfl
    subst heq_outputs
    simp at houtputs₁' houtputs₂'
    simp [← houtputs₁', ← houtputs₂']
    apply forall₂_to_forall₂_push_toList
    · simp [EqModGhost]
    · simp [EqModGhost]
  case yield.yield.triv_join.triv_join.join =>
    intros
    rename_i houtputs₁ _ _ _ _ houtputs₂
    simp [← houtputs₁, ← houtputs₂, Vector.toList_map, EqModGhost]
    apply List.forall₂_iff_get.mpr
    simp

theorem proc_guard_spec_strong_confl_at
  [Arity Op] [PCM T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n)
  (s : proc.semantics.S)
  (haff : s.proc.AffineChan) :
    (proc.semantics.guard (opSpec.Guard ioSpec)).lts.StronglyConfluentAt
      Label.IsYieldOrSilentAndDet
      s
  := by
  have hconfl_base : Lts.StronglyConfluentAt _ _ _ :=
    proc_strong_confl_at proc s haff
  have hconfl_guard : Lts.StronglyConfluentAt _ _ _ :=
    guard_strong_confl_at
      (Op := WithSpec Op opSpec) (Op' := Op)
      (Guard := opSpec.Guard ioSpec)
      proc.semantics s op_spec_guard_eq_congr hconfl_base
  apply Lts.strong_confl_at_imp_compat
    (Compat₁ := λ l₁' l₂' => ∀ {l₁ l₂},
      opSpec.Guard ioSpec l₁ l₁' →
      opSpec.Guard ioSpec l₂ l₂' →
      Label.IsYieldOrSilentAndDet l₁ l₂)
  · intros l₁' l₂' hcompat l₁ l₂
    apply guard_label_compat_inversion hcompat
  · exact hconfl_guard

theorem proc_guard_triv_strong_confl_at_mod
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  (proc : ProcWithSpec opSpec χ m n)
  (s : proc.semantics.S)
  (haff : s.proc.AffineChan) :
    (proc.semantics.guard opSpec.TrivGuard).lts.StronglyConfluentAtMod
      Label.IsYieldOrSilentAndDet
      (Config.EqMod EqModGhost)
      Eq
      s
  := by
  have hconfl_base : Lts.StronglyConfluentAtMod _ _ _ _ _ :=
    proc_strong_confl_at_mod EqModGhost proc s haff
  have hconfl_guard : Lts.StronglyConfluentAtMod _ _ _ _ _ :=
    guard_strong_confl_at_mod
      (Op := WithSpec Op opSpec) (Op' := Op)
      (Guard := opSpec.TrivGuard)
      (EqS := Config.EqMod EqModGhost)
      (EqL := Label.EqMod EqModGhost)
      (EqL' := Eq)
      (Compat := Label.IsYieldOrSilentAndDetMod EqModGhost)
      proc.semantics s
      op_spec_triv_guard_eq_congr
      hconfl_base
  apply Lts.strong_confl_at_mod_imp_compat
    (Compat₁ := λ l₁' l₂' => ∀ {l₁ l₂},
      opSpec.TrivGuard l₁ l₁' →
      opSpec.TrivGuard l₂ l₂' →
      Label.IsYieldOrSilentAndDetMod EqModGhost l₁ l₂)
  · intros l₁' l₂' hcompat l₁ l₂
    apply guard_label_triv_compat_inversion hcompat
  · exact hconfl_guard

theorem pop_vals_disj_preserves_pairwise
  [DecidableEq χ]
  {map : ChanMap χ V}
  {P : V → V → Prop}
  {names₁ : Vector χ m} {vals₁ : Vector V m}
  {names₂ : Vector χ n} {vals₂ : Vector V n}
  (hpw : map.Pairwise P)
  (hdisj : List.Disjoint names₁.toList names₂.toList)
  (hpop₁ : map.popVals names₁ = some (vals₁, map'))
  (hpop₂ : map.popVals names₂ = some (vals₂, map'')) :
    ∀ v₁ v₂, v₁ ∈ vals₁ → v₂ ∈ vals₂ → P v₁ v₂
  := sorry

/--
Strong confluence of a `ProcWithSpec` when interpreted with
a sound and deterministic interpretation.

TODO: this is probably generalizable to a general confluent `Semantics`.
-/
theorem proc_interp_strong_confl_at
  [Arity Op]
  [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {opInterp : OpInterp Op V}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n)
  -- Sound (wrt. opSpec) and deterministic interpretation
  (hsound : OpSpec.Sound opSpec opInterp)
  (hdet : opInterp.Deterministic)
  (s : proc.semantics.S)
  (t : opInterp.S)
  -- Some required state invariants
  (haff : s.proc.AffineChan)
  (hdisj : s.DisjointTokens) :
    ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.StronglyConfluentAt
      (λ l₁ l₂ => l₁.isSilent ∧ l₂.isSilent)
      (s, t)
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  rcases s₁' with ⟨s₁', t₁'⟩
  rcases s₂' with ⟨s₂', t₂'⟩
  cases hstep₁ <;> cases hstep₂ <;> simp at hcompat
  case step_tau.step_tau hstep₁ hstep₂ =>
    have := proc_guard_spec_strong_confl_at proc s haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq => simp [heq]
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t)
      exact ⟨
        InterpStep.step_tau hstep₁',
        InterpStep.step_tau hstep₂'
      ⟩
  case step_tau.step_yield hstep₁ _ _ _ hstep₂ hstep_op₂ =>
    have := proc_guard_spec_strong_confl_at proc s haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq => simp at heq
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t₂')
      exact ⟨
        InterpStep.step_yield hstep₁' hstep_op₂,
        InterpStep.step_tau hstep₂',
      ⟩
  case step_yield.step_tau _ _ _ _ hstep₁ hstep_op₁ hstep₂ =>
    have := proc_guard_spec_strong_confl_at proc s haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq => simp at heq
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t₁')
      exact ⟨
        InterpStep.step_tau hstep₁',
        InterpStep.step_yield hstep₂' hstep_op₁,
      ⟩
  case step_yield.step_yield
    op₁ inputVals₁ _ hstep₁ hstep_op₁
    op₂ inputVals₂ _ hstep₂ hstep_op₂ =>
    have hconfl_sem := proc_guard_spec_strong_confl_at proc s haff hstep₁ hstep₂
      (by
        -- By `hdet`
        simp only [Label.IsYieldOrSilentAndDet, Label.Deterministic]
        and_intros
        · simp
        · simp
        · intros op inputVals outputVals₁ outputVals₂ heq_yield₁ heq_yield₂
          simp at heq_yield₁ heq_yield₂
          have ⟨heq_op₁, heq_inputs₁, heq_outputs₁⟩ := heq_yield₁
          have ⟨heq_op₂, heq_inputs₂, heq_outputs₂⟩ := heq_yield₂
          subst heq_op₁; subst heq_inputs₁; subst heq_outputs₁
          subst heq_op₂; subst heq_inputs₂; subst heq_outputs₂
          simp [hdet hstep_op₁ hstep_op₂])
    cases hconfl_sem with
    | inl heq =>
      left
      simp at heq
      have ⟨⟨h₁, h₂, h₃⟩, h₄⟩ := heq
      subst h₁; subst h₂; subst h₃
      simp [h₄, hdet hstep_op₁ hstep_op₂]
    | inr h =>
      cases hstep₁ with | step hguard₁ hstep₁ =>
      cases hstep₂ with | step hguard₂ hstep₂ =>
      cases hguard₁ with | spec_yield =>
      -- rename_i tok₁ tok₁'
      cases hguard₂ with | spec_yield =>
      -- rename_i tok₂ tok₂'
      cases hstep₁ with | step_op hmem₁ hpop₁ =>
      cases hstep₂ with | step_op hmem₂ hpop₂ =>
      have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem₁
      have ⟨j, hj, hget_j⟩ := List.getElem_of_mem hmem₂
      by_cases heq_ij : i = j
      · -- Firing the same atom, so the result must be the same by `hdet`
        left
        subst heq_ij
        simp [hget_i] at hget_j
        have ⟨h₁, h₂, h₃⟩ := hget_j
        subst h₁; subst h₂; subst h₃
        simp [hpop₁, Vector.push_eq_push] at hpop₂
        have ⟨⟨h₄, h₅⟩, h₆⟩ := hpop₂
        replace h₅ := Vector.inj_map (by simp [Function.Injective]) h₅
        subst h₅; subst h₆
        -- simp [h₄, htok₁', htok₂']
        have ⟨h₇, h₈⟩ := hdet hstep_op₁ hstep_op₂
        subst h₈
        constructor
        · rfl
        · simp [h₇]
      · right
        have ⟨t', hstep_op₁', hstep_op₂'⟩ := hsound hstep_op₁ hstep_op₂
          (by
            -- Firing different atoms, so the tokens must be disjoint by `DisjointTokens`.
            simp [OpSpec.CompatLabels]
            -- apply PCM.eq_congr_disj htok₁ htok₂
            have := haff.atom_inputs_disjoint ⟨i, hi⟩ ⟨j, hj⟩ (by simp [heq_ij])
            simp [hget_i, hget_j, AtomicProc.inputs] at this
            have := pop_vals_disj_preserves_pairwise hdisj this hpop₁ hpop₂
            -- have := this (.inr _) (.inr _)
            apply this (.inr (opSpec.pre op₁ inputVals₁)) (.inr (opSpec.pre op₂ inputVals₂))
            all_goals simp)
        replace ⟨s', hstep₁', hstep₂'⟩ := h
        exists (s', t')
        exact ⟨
          InterpStep.step_yield hstep₁' hstep_op₁',
          InterpStep.step_yield hstep₂' hstep_op₂',
        ⟩

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

/-- `Config.DisjointTokens` is a state invariant of a guarded `Fn` semantics. -/
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

/-
TODO:

Translating confluence result in the guarded semantics
to the unguarded semantics:

1. If there is a trace in the guarded semantics from `s`,
   and `s ≈ s'` modulo ghost tokens, then there is a trace
   in the unguarded semantics from `s'` to the same state
   modulo ghost tokens.

2. If there is a trace in the guarded semantics from `s` to `s'`
   such that `s'` is final in the *unguarded semantics*, then
   any unguarded step from `s` to other `s''` can be converted
   to a guarded trace modulo ghost tokens.

We know that for a `proc` and good `s`

- proc_strong_confl_at:
    `proc.semantics.StronglyConfluentAt s`
- proc_guard_spec_strong_confl_at:
    `(proc.semantics.guard (opSpec.Guard ioSpec)).StronglyConfluentAt IsYieldOrSilentAndDet s`
- proc_guard_triv_strong_confl_at_mod:
    `(proc.semantics.guard opSpec.TrivGuard).StronglyConfluentAtMod IsYieldOrSilentAndDet EqModGhost s`
- proc_interp_strong_confl_at:
    `((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).StronglyConfluentAt
      (λ l₁ l₂ => l₁.isSilent ∧ l₂.isSilent) (s, t)`
-/

-- theorem hmm?
--   {lts₁ lts₂ : Lts C E}
--   {tr : Trace E}
--   {c₁ c₂ c₁' : C}
--   {Labels : E → Prop}
--   {EqC : C → C → Prop}
--   (htrace₁ : lts₁.Star c₁ tr c₁')
--   (htr : ∀ l ∈ tr, Labels l)
--   (hterm : lts₂.IsFinalFor Labels c₁')

--   (heq : EqC c₁ c₂)

--   : True := sorry

-- theorem hmm
--   [Arity Op] [Arity Op']
--   {opInterp : OpInterp Op' V'}
--   {sem : Semantics Op V m n}
--   {s s' s₁' sₜ : sem.S × opInterp.S}
--   {Compat : Label Op V m n → Label Op V m n → Prop}
--   {EqS : sem.S → sem.S → Prop}
--   {Guard₁ Guard₂ : Label Op V m n → Label Op' V' m' n' → Prop}
--   (hconfl_sem : sem.lts.StronglyConfluentAt Compat s.1)

--   -- (hguard_compat₁ : ∀ {l₁ l₂ l₁' l₂'},
--   --   l₁'.isYield ∨ l₁'.isSilent →
--   --   l₂'.isYield ∨ l₂'.isSilent →
--   --   Guard₁ l₁ l₁' →
--   --   Guard₁ l₂ l₂' →
--   --   Compat l₁ l₂)

--   -- (hguard_compat₂ : ∀ {l₁ l₂ l₁' l₂'},
--   --   l₁'.isYield ∨ l₁'.isSilent →
--   --   l₂'.isYield ∨ l₂'.isSilent →
--   --   Guard₂ l₁ l₁' →
--   --   Guard₂ l₂ l₂' →
--   --   Compat l₁ l₂)

--   (hconfl_interp : ((sem.guard Guard₁).interpret opInterp).lts.StronglyConfluentAt
--     (λ l₁ l₂ => l₁.isSilent ∧ l₂.isSilent)
--     s)

--   -- A dominating trace
--   (htrace₁ : ((sem.guard Guard₁).interpret opInterp).lts.TauStar .τ s sₜ)
--   (hterm : sem.IsFinalFor (·.isSilent) sₜ.1)

--   (heq : EqS s.1 s'.1 ∧ s.2 = s'.2)
--   (hstep₂ : ((sem.guard Guard₂).interpret opInterp).lts.Step s' .τ s₁') :
--     ∃ sₜ',
--       ((sem.guard Guard₂).interpret opInterp).lts.TauStar .τ s₁' sₜ' ∧
--       EqS sₜ.1 sₜ'.1 ∧
--       sₜ.2 = sₜ'.2
--   := sorry

/-- Special case restricted to a single label `τ`. -/
theorem strong_confl_final_confl_tau
  {lts : Lts C E} {c : C} {τ : E}
  {Compat : E → E → Prop}
  (hinv : lts.IsInvariantAt (lts.StronglyConfluentAt Compat) c)
  (htau : ∀ {l l'}, Compat l l' ↔ l = τ ∧ l' = τ)
  (hsteps₁ : lts.TauStar τ c c₁)
  (hterm : lts.IsFinalFor (· = τ) c₁)
  (hstep₂ : lts.Step c τ c₂) : lts.TauStar τ c₂ c₁
  := by
  induction hsteps₁
    using Lts.TauStar.reverse_induction
    generalizing c₂ with
  | refl =>
    exact False.elim (hterm (by rfl) hstep₂)
  | head hstep₁ htail₁ ih =>
    rename_i c c'
    have ⟨hconfl', hinv'⟩ := hinv.step hstep₁
    have := hinv.base hstep₁ hstep₂ (by simp [htau])
    cases this with
    | inl heq => simp [← heq, htail₁]
    | inr h =>
      have ⟨c'', hstep₁', hstep₂'⟩ := h
      have := ih hinv' hstep₁'
      exact this.prepend hstep₂'

-- theorem proc_guarded_weak_normalization_confl
--   [Arity Op] [PCM T] [PCM.Lawful T]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {opSpec : OpSpec Op V T}
--   {opInterp : OpInterp Op V}
--   {ioSpec : IOSpec V T m n}
--   (proc : ProcWithSpec opSpec χ m n)
--   {s s₁ s₂ : proc.semantics.S × opInterp.S}
--   (htrace₁ : ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.TauStar .τ s s₁)
--   (hterm : proc.semantics.IsFinal s₁.1)
--   (hstep₂ : ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.Step s .τ s₂) :
--     ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.TauStar .τ s₂ s₁
--   := by
--   induction htrace₁
--     using Lts.TauStar.reverse_induction with
--   | refl =>
--     match hstep₂ with
--     | .step_tau hstep₂ =>
--       cases hstep₂ with | step _ hstep₂ =>
--       exact False.elim (hterm hstep₂)
--     | .step_yield hstep₂ _ =>
--       cases hstep₂ with | step _ hstep₂ =>
--       exact False.elim (hterm hstep₂)
--   | head hstep₁ htail₁ ih =>
--     rename_i s s'
--     apply ih
--     sorry

theorem proc_guarded_weak_normalization'
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {opInterp : OpInterp Op V}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n)
  (s s₁ s₂ : proc.semantics.S × opInterp.S)
  (htrace₁ : ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.TauStar
    .τ s s₁)
  (hterm : proc.semantics.IsFinal s₁.1)
  (htrace₂ : ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.TauStar
    .τ s s₂) :
    ∃ s₁',
      ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.TauStar
        .τ s₂ s₁' ∧
      Config.EqMod EqModGhost s₁.1 s₁'.1 ∧
      s₁.2 = s₁'.2
  := by
  -- Naming convension:
  -- s : proc.semantics.S × opInterp.S
  -- c : proc.semantics.S
  -- t : opInterp.S
  induction htrace₁
    using Lts.TauStar.reverse_induction with
  | refl =>
    induction htrace₂
      using Lts.TauStar.reverse_induction with
    | refl =>
      exists s₂
      and_intros
      · exact .refl
      · rfl
      · apply IsRefl.refl
      · rfl
    | head hstep₂ =>
      match hstep₂ with
      | .step_tau hstep₂ =>
        cases hstep₂ with | step hguard hstep₂ =>
        cases hguard <;> exact False.elim (hterm hstep₂)
      | .step_yield hstep₂ _ =>
        cases hstep₂ with | step hguard hstep₂ =>
        cases hguard
        exact False.elim (hterm hstep₂)
  | head hstep₁ htail₁ ih₁ =>
    induction htrace₂
      using Lts.TauStar.reverse_induction with
    | refl =>
      have htrace₁ := htail₁.prepend hstep₁
      replace htrace₁ := htrace₁.map
        (λ hstep => hstep.map_step (Guard.map_guard OpSpec.spec_guard_implies_triv_guard))
      exists s₁
      and_intros
      · exact htrace₁
      · rfl
      · apply IsRefl.refl
      · rfl
    | head hstep₂ htail₂ ih₂ =>
      case head.head =>
      rename_i _ s₁'' s s₂''
      have hstep₁' := hstep₁.map_step (Guard.map_guard OpSpec.spec_guard_implies_triv_guard)
      have haff : s.1.proc.AffineChan := sorry
      -- have hconfl := proc_guard_triv_strong_confl_at_mod proc s.1 haff hstep₁' hstep₂
      cases hstep₁' <;> cases hstep₂
      case step_tau.step_tau c c₁ t hstep₁' c₂ hstep₂ =>
        have hconfl := proc_guard_triv_strong_confl_at_mod proc _ haff hstep₁' hstep₂
          (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
        cases hconfl with
        | inl heq => sorry
        | inr h =>

          sorry
      all_goals sorry

/-- Turns a guarded trace of τ steps into an unguarded one
one a state `EqModGhost` to the original state. -/
theorem proc_guarded_steps_congr_eq_mod
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {opInterp : OpInterp Op V}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n)
  {s₁ s₁' s₂ : proc.semantics.S × opInterp.S}
  (htrace₁ : ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.TauStar .τ s₁ s₂)
  (heq : Config.EqMod EqModGhost s₁.1 s₁'.1 ∧ s₁.2 = s₁'.2) :
    ∃ s₂',
      ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.TauStar .τ s₁' s₂' ∧
      Config.EqMod EqModGhost s₂.1 s₂'.1 ∧
      s₂.2 = s₂'.2
  := by
  sorry

/--
If there is a guarded τ trace from `s` to a final state `s₁`,
then we can turn any *unguarded* τ step from `s` to `s₂`,
into a guarded τ step, modulo potentially different ghost tokens.
-/
theorem proc_unguarded_to_guarded
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n)
  {s s₁ s₂ : proc.semantics.S}
  {tr : List (Label Op V m n)}
  {l : Label Op V m n}
  (htrace₁ : (proc.semantics.guard (opSpec.Guard ioSpec)).lts.Star s tr s₁)
  (htr : ∀ l ∈ tr, l.isSilent ∨ l.isYield)
  (hterm : proc.semantics.IsFinalFor (λ l => l.isSilent ∨ l.isYield) s₁)
  (hstep₂ : (proc.semantics.guard opSpec.TrivGuard).lts.Step s l s₂)
  (hl : l.isSilent ∨ l.isYield) :
    ∃ s₂',
      (proc.semantics.guard (opSpec.Guard ioSpec)).lts.Step s l s₂' ∧
      Config.EqMod EqModGhost s₂' s₂
  := by
  induction htrace₁
    using Lts.Star.reverse_induction with
  | refl =>
    cases hstep₂ with | step hguard hstep₂ =>
    cases l <;> simp at hl
    all_goals
      cases hguard <;> exact False.elim (hterm (by simp) hstep₂)
  | head hstep₁ htail₁ ih =>
    rename_i s s' l' tr'
    have hl' := htr l' (by simp)
    cases l <;> simp at hl
    case yield op inputVals outputVals =>
      cases l' <;> simp at hl'
      case yield op' inputVals' outputVals' =>
        sorry
      case τ =>
        sorry
    case τ =>
      sorry

/--
If there is a guarded τ trace from `s` to a final state `s₁`,
then we can turn any *unguarded* τ step from `s` to `s₂`,
into a guarded τ step, modulo potentially different ghost tokens.
-/
theorem proc_unguarded_to_guarded_interp
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {opInterp : OpInterp Op V}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n)
  {s s₁ s₂ : proc.semantics.S × opInterp.S}
  (htrace₁ : ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.TauStar
    .τ s s₁)
  -- Note: this has to require that `s'` is final in the original, unguarded semantics
  (hterm : proc.semantics.IsFinalFor (λ l => l.isSilent ∨ l.isYield) s₁.1)
  (hstep₂ : ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.Step s .τ s₂) :
    ∃ s₂',
      ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.Step s .τ s₂' ∧
      Config.EqMod EqModGhost s₂'.1 s₂.1 ∧
      s₂'.2 = s₂.2
  := by
  induction htrace₁
    using Lts.TauStar.reverse_induction with
  | refl =>
    match hstep₂ with
    | .step_tau hstep₂ =>
      cases hstep₂ with | step hguard hstep₂ =>
      cases hguard <;> exact False.elim (hterm (by simp) hstep₂)
    | .step_yield hstep₂ _ =>
      cases hstep₂ with | step hguard hstep₂ =>
      cases hguard
      exact False.elim (hterm (by simp) hstep₂)
  | head hstep₁ htail₁ ih =>
    rename_i s s'

    sorry

theorem proc_guarded_weak_normalization
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {opInterp : OpInterp Op V}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n)
  {s s₁' s₂' : proc.semantics.S}
  {t t₁' t₂' : opInterp.S}
  (htrace₁ : ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.TauStar
    .τ (s, t) (s₁', t₁'))
  (htrace₂ : ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.TauStar
    .τ (s, t) (s₂', t₂'))
  -- Note: this has to require that `s'` is final in the original, unguarded semantics
  (hterm : proc.semantics.IsFinal s₁') :
    ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.TauStar
      .τ (s₂', t₂') (s₁', t₁')
    -- TODO: prove that `htrace₂` is bounded (strong normalization)
  := by
  -- Sketch:
  -- 1. Take the first transition of both `htrace₁` and `htrace₂`
  -- 2. If they are the same, recurse
  -- 3. If they are different, the same op fired in `htrace₁` must be
  --    fired at some point in `htrace₁` with valid tokens (otherwise
  --    it violates `hterm`). Use a separate lemma to commute that future
  --    step back to the first (using `proc_interp_strong_confl_at_mod`)
  --    and recurse.
  sorry

end Wavelet.Compile

namespace Wavelet.Seq

open Semantics

/-- Simple non-dependent resource specs. -/
structure SimpleOpSpec Op T where
  pre : Op → T
  post : Op → T
  -- frame_preserving : ∀ op, pre op ⟹ post op

def SimpleOpSpec.toOpSpec
  V [Arity Op] (spec : SimpleOpSpec Op T) :
  Semantics.OpSpec Op V T := {
    pre op _ := spec.pre op,
    post op _ _ := spec.post op,
    -- frame_preserving := by intros; apply spec.frame_preserving
  }

structure SimpleIOSpec T where
  pre : T
  post : T

def SimpleIOSpec.toIOSpec (spec : SimpleIOSpec T) m n :
  IOSpec V T m n := {
    pre _ := spec.pre,
    post _ := spec.post,
  }

/-- `.inl` for base vars, `.inr` for token variables. -/
abbrev TypedName χ := χ ⊕ Nat

/-- Map from ghost variable names to their concrete permission. -/
structure PermCtx T where
  perms : VarMap Nat T
  numVars : Nat

/-- Insert `n` new permission tokens and return the fresh indices -/
def PermCtx.insertVars
  (ctx : PermCtx T) (tys : Vector T n) :
  Vector Nat n × PermCtx T :=
  let newIdxs := Vector.range' ctx.numVars n
  (newIdxs, {
    perms := ctx.perms.insertVars newIdxs tys,
    numVars := ctx.numVars + n
  })

def PermCtx.removeVars
  (ctx : PermCtx T) (idxs : List Nat) : PermCtx T :=
  { ctx with perms := ctx.perms.removeVars idxs }

/-- Initial context with a single permission variable. -/
def PermCtx.init
  (init : T) : PermCtx T := {
    perms idx := if idx = 0 then some init else none,
    numVars := 1
  }

/-- Defines when a (disjoint) list of variable indices
has a total permission equal to the sum of `req` and `rem`. -/
def PermCtx.Acquire
  [PCM T]
  (ctx : PermCtx T)
  (req rem : T)
  (tokIds : Vector Nat k)
  (toks : Vector T k) : Prop :=
  tokIds.toList.Nodup ∧
  ctx.perms.getVars tokIds = some toks ∧
  req ⊔ rem = PCM.sum toks.toList

/-- Relational definition for a function to be well-typed
as a more elaborated `FnWithSpec` with explicit permissions. -/
inductive Expr.WellPermTyped
  [Arity Op] [PCM T]
  {opSpec : SimpleOpSpec Op T}
  (ioSpec : SimpleIOSpec T) :
  PermCtx T → Expr Op χ m n →
  ExprWithSpec (opSpec.toOpSpec V) (TypedName χ) m n → Prop where
  | wpt_ret {joined ctx' ctx vars rem}
    (k : Nat) {tokIds : Vector Nat k} {toks : Vector T k} :
    ctx.Acquire ioSpec.post rem tokIds toks →
    ctx.insertVars #v[ioSpec.post, rem] = (joined, ctx') →
    WellPermTyped ioSpec ctx
      (.ret vars)
      (.op (.join k 0 (λ _ => ioSpec.post)) (tokIds.map .inr) (joined.map .inr)
        (.ret ((vars.map .inl).push (.inr joined[0]))))
  | wpt_tail {joined ctx' ctx args rem}
    (k : Nat) {tokIds : Vector Nat k} {toks : Vector T k} :
    -- The returned permission should exactly match since the token is non-dependent
    ctx.Acquire ioSpec.pre rem tokIds toks →
    ctx.insertVars #v[ioSpec.pre, rem] = (joined, ctx') →
    WellPermTyped ioSpec ctx
      (.tail args)
      (.op (.join k 0 (λ _ => ioSpec.pre)) (tokIds.map .inr) (joined.map .inr)
        (.tail ((args.map .inl).push (.inr joined[0]))))
  | wpt_op {ctx' joined ctx'' cont cont' ctx o args rem}
    {bind}
    (k : Nat) {tokIds : Vector Nat k} {toks : Vector T k} :
    ctx.Acquire (opSpec.pre o) rem tokIds toks →
    ctx.removeVars tokIds.toList = ctx' →
    ctx'.insertVars #v[opSpec.pre o, rem, opSpec.post o] = (joined, ctx'') →
    WellPermTyped ioSpec (ctx''.removeVars [joined[0]]) cont cont' →
    WellPermTyped ioSpec ctx
      (.op o args bind cont)
      (.op (.join k 0 (λ _ => opSpec.pre o)) -- First call join to collect required permissions
        (tokIds.map .inr)
        #v[.inr joined[0], .inr joined[1]]
        (.op (.op o) -- Then call the actual operator
          ((args.map .inl).push (.inr joined[0]))
          ((bind.map .inl).push (.inr joined[2])) cont'))
  | wpt_br {ctx cond left left' right right'} :
    WellPermTyped ioSpec ctx left left' →
    WellPermTyped ioSpec ctx right right' →
    WellPermTyped ioSpec ctx (.br cond left right) (.br (.inl cond) left' right')

def Fn.WellPermTyped
  [Arity Op] [PCM T]
  {opSpec : SimpleOpSpec Op T}
  (ioSpec : SimpleIOSpec T)
  (fn : Fn Op χ V m n)
  (fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n) :
  Prop :=
  fn'.params = (fn.params.map .inl).push (.inr 0) ∧
  Expr.WellPermTyped ioSpec (.init (ioSpec.pre)) fn.body fn'.body

def SimRel
  [Arity Op] [PCM T]
  {opSpec : SimpleOpSpec Op T}
  (ioSpec : SimpleIOSpec T)
  (s₁ : Config Op χ V m n)
  (s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)) :
  Prop :=
  s₁.fn.WellPermTyped ioSpec s₂.fn ∧
  s₂.DisjointTokens ∧
  (s₁.cont = .init → s₂.cont = .init) ∧
  (∀ expr,
    s₁.cont = .expr expr →
    ∃ ctx expr₂,
      s₂.cont = .expr expr₂ ∧
      Expr.WellPermTyped ioSpec ctx expr expr₂ ∧
      s₂.vars = VarMap.disjointUnion s₁.vars ctx.perms)

/-! Lemmas. TODO: move to somewhere else -/
section Lemmas

theorem var_map_disjoint_union_get_vars_left
  {m₁ : VarMap χ₁ V₁}
  {m₂ : VarMap χ₂ V₂}
  (hget : m₁.getVars vars = some vals) :
  (VarMap.disjointUnion m₁ m₂).getVars (vars.map .inl) = some (vals.map .inl)
  := sorry

theorem var_map_disjoint_union_get_var_left
  {m₁ : VarMap χ₁ V₁}
  {m₂ : VarMap χ₂ V₂}
  (hget : m₁.getVar var = some val) :
  (VarMap.disjointUnion m₁ m₂).getVar (.inl var) = some (.inl val)
  := sorry

theorem var_map_disjoint_union_get_vars_right
  {m₁ : VarMap χ₁ V₁}
  {m₂ : VarMap χ₂ V₂}
  (hget : m₂.getVars vars = some vals) :
  (VarMap.disjointUnion m₁ m₂).getVars (vars.map .inr) = some (vals.map .inr)
  := sorry

theorem var_map_init_disjoint_tokens
  [DecidableEq χ] [PCM T]
  {vars : Vector χ (n + 1)}
  {args : Vector V n}
  {tok : T} :
  (VarMap.fromList (vars.zip ((args.map .inl).push (.inr tok))).toList).DisjointTokens
:= sorry

end Lemmas

theorem sim_type_check_init
  [Arity Op]
  [InterpConsts V]
  [PCM T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  (hwt : fn.WellPermTyped ioSpec fn') :
    SimRel ioSpec
      fn.semantics.init
      (fn'.semantics.guard ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).init
  := by
  simp [Fn.semantics, Semantics.guard, Semantics.guard, Config.init]
  simp [Fn.WellPermTyped] at hwt
  and_intros
  · simp [hwt]
  · simp [hwt]
  · simp [VarMap.DisjointTokens]
  · simp
  · simp

theorem sim_type_check_input_vars
  [DecidableEq χ] [PCM T]
  {params : Vector χ n}
  {args : Vector V n}
  {tok : T} :
    VarMap.fromList
      (((params.map .inl).push (.inr 0)).zip
        ((args.map .inl).push (.inr tok))).toList =
    VarMap.disjointUnion (VarMap.fromList (params.zip args).toList) (PermCtx.init tok).perms
  := sorry

theorem sim_type_check_input
  [Arity Op]
  [InterpConsts V]
  [PCM T] [pcm : PCM.Lawful T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  {s₁ s₁' : Config Op χ V m n}
  {s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)}
  {l : Label Op V m n}
  (hsim : SimRel ioSpec s₁ s₂)
  (hcont : s₁.cont = .init)
  (hstep : fn.semantics.lts.Step s₁ l s₁') :
    ∃ s₂',
      (fn'.semantics.guard
        ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep
        .τ s₂ l s₂' ∧
      SimRel ioSpec s₁' s₂'
  := by
  have ⟨hwt_fn, hdisj, hinit, _⟩ := hsim
  cases hstep with
  | step_ret hexpr | step_tail hexpr
  | step_op hexpr | step_br hexpr => simp [hcont] at hexpr
  | step_init =>
  rename Vector V m => args
  have hcont₂ := hinit hcont
  simp [Fn.semantics, Semantics.guard, Semantics.guard, Config.init]
  have hstep₂ :
    (fn'.semantics.guard
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.Step
      s₂ (.input args) _ :=
    guard_single
      (by
        apply OpSpec.Guard.spec_input)
      (.step_init
        (args := (args.map .inl).push (.inr ioSpec.pre))
        hcont₂)
  exact ⟨_, .single hstep₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · exact var_map_init_disjoint_tokens
      · simp
      · simp
        exists PermCtx.init ioSpec.pre
        and_intros
        · simp [hwt_fn.2]
        · simp [hwt_fn.1]
          apply sim_type_check_input_vars
  ⟩

theorem sim_type_check_ret
  [Arity Op]
  [InterpConsts V]
  [PCM T] [pcm : PCM.Lawful T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  {s₁ s₁' : Config Op χ V m n}
  {s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)}
  {l : Label Op V m n}
  (hsim : SimRel ioSpec s₁ s₂)
  (hret : s₁.cont = .expr (.ret vars))
  (hstep : fn.semantics.lts.Step s₁ l s₁') :
    ∃ s₂',
      (fn'.semantics.guard
        ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep
        .τ s₂ l s₂' ∧
      SimRel ioSpec s₁' s₂'
  := by
  have ⟨hwt_fn, hdisj, _, hcont⟩ := hsim
  cases hstep with
  | step_init hexpr | step_tail hexpr
  | step_op hexpr | step_br hexpr => simp [hret] at hexpr
  | step_ret hexpr hget_vars =>
  rename_i retVals vars
  have ⟨ctx, expr₂, hcont₂, hwt, hvars⟩ := hcont _ hexpr
  cases hwt with | wpt_ret k hacq hins =>
  rename Vector T k => toks
  rename Vector ℕ k => tokIds
  rename Vector ℕ 2 => joined
  rename T => rem
  have ⟨hacq₁, hacq₂, hacq₃⟩ := hacq
  -- Join required permissions
  have hstep₂ :
    (fn'.semantics.guard
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.Step
      s₂ _ _ :=
    guard_single
      (e' := .τ)
      (.spec_join (vals := #v[]) (by rfl) (by rfl) hacq₃)
      (.step_op (outputVals := #v[.inr ioSpec.post, .inr rem])
        hcont₂
        (by
          simp [hvars]
          apply var_map_disjoint_union_get_vars_right hacq₂))
  -- Run the actual return expression
  have hsteps₂ :
    (fn'.semantics.guard
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep .τ
      s₂ (.output retVals) _ := (Lts.WeakStep.single hstep₂).tail_non_tau
    (guard_single
      (by
        apply OpSpec.Guard.spec_output)
      (.step_ret (retVals := (retVals.map .inl).push (.inr ioSpec.post))
        (by rfl)
        (by
          simp
          -- TODO: some var map manipulation
          sorry)))
  simp at hsteps₂
  exact ⟨_, hsteps₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · simp [VarMap.DisjointTokens]
      · simp
      · simp
  ⟩

theorem sim_type_check_tail
  [Arity Op]
  [InterpConsts V]
  [PCM T] [pcm : PCM.Lawful T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  {s₁ s₁' : Config Op χ V m n}
  {s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)}
  {l : Label Op V m n}
  (hsim : SimRel ioSpec s₁ s₂)
  (htail : s₁.cont = .expr (.tail vars))
  (hstep : fn.semantics.lts.Step s₁ l s₁') :
    ∃ s₂',
      (fn'.semantics.guard
        ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep
        .τ s₂ l s₂' ∧
      SimRel ioSpec s₁' s₂'
  := by
  have ⟨hwt_fn, hdisj, _, hcont⟩ := hsim
  cases hstep with
  | step_init hexpr | step_ret hexpr
  | step_op hexpr | step_br hexpr => simp [htail] at hexpr
  | step_tail hexpr hget_vars =>
  rename_i tailArgs vars
  have ⟨ctx, expr₂, hcont₂, hwt, hvars⟩ := hcont _ hexpr
  cases hwt with | wpt_tail k hacq hins =>
  rename Vector T k => toks
  rename Vector ℕ k => tokIds
  rename Vector ℕ 2 => joined
  rename T => rem
  have ⟨hacq₁, hacq₂, hacq₃⟩ := hacq
  -- Join required permissions
  have hstep₂ :
    (fn'.semantics.guard
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.Step
      s₂ _ _ :=
    guard_single
      (.spec_join (vals := #v[]) (by rfl) (by rfl) hacq₃)
      (.step_op (outputVals := #v[.inr ioSpec.pre, .inr rem])
        hcont₂
        (by
          simp [hvars]
          apply var_map_disjoint_union_get_vars_right hacq₂))
  -- Run the actual return expression
  have hsteps₂ :
    (fn'.semantics.guard
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep .τ
      s₂ .τ _ := (Lts.WeakStep.single hstep₂).tail_non_tau
    (guard_single
      .spec_tau
      (.step_tail (tailArgs := (tailArgs.map .inl).push (.inr ioSpec.pre))
        (by rfl)
        (by
          simp
          -- TODO: some var map manipulation
          sorry)))
  simp at hsteps₂
  exact ⟨_, hsteps₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · simp
        sorry
      · simp
      · simp
        exists PermCtx.init ioSpec.pre
        and_intros
        · simp [hwt_fn.2]
        · simp [hwt_fn.1]
          apply sim_type_check_input_vars
  ⟩

theorem sim_type_check_op
  [Arity Op]
  [InterpConsts V]
  [PCM T] [pcm : PCM.Lawful T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  {s₁ s₁' : Config Op χ V m n}
  {s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)}
  {l : Label Op V m n}
  {bind cont' args}
  (hsim : SimRel ioSpec s₁ s₂)
  (hret : s₁.cont = .expr (.op op args bind cont'))
  (hstep : fn.semantics.lts.Step s₁ l s₁') :
    ∃ s₂',
      (fn'.semantics.guard
        ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep
        .τ s₂ l s₂' ∧
      SimRel ioSpec s₁' s₂'
  := by
  have ⟨hwt_fn, hdisj, _, hcont⟩ := hsim
  cases hstep with
  | step_init hexpr | step_tail hexpr
  | step_ret hexpr | step_br hexpr => simp [hret] at hexpr
  | step_op hexpr hget_vars =>
  rename_i op inputVals outputVals args bind cont
  have ⟨ctx, expr₂, hcont₂, hwt, hvars⟩ := hcont _ hexpr
  cases hwt with | wpt_op k hacq hremove hins hwt' =>
  rename T => rem
  have ⟨hacq₁, hacq₂, hacq₃⟩ := hacq
  -- Join permissions
  have hstep₂ :
    (fn'.semantics.guard
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.Step
      s₂ .τ _ :=
    guard_single
      (.spec_join (vals := #v[]) (by rfl) (by rfl) hacq₃)
      (.step_op (outputVals := #v[.inr (opSpec.pre op), .inr rem])
        hcont₂
        (by
          simp [hvars]
          apply var_map_disjoint_union_get_vars_right hacq₂))
  replace ⟨s₂', hstep₂, hs₂'⟩ := exists_eq_right.mpr hstep₂
  have hstep₂' :
    fn'.semantics.lts.Step s₂' (.yield (.op _) _ _) _
    := .step_op
        (inputVals := (inputVals.map Sum.inl).push (.inr (opSpec.pre op)))
        (outputVals := (outputVals.map Sum.inl).push (.inr (opSpec.post op)))
        (by simp only [hs₂']; rfl)
        (by
          -- TODO: var map manipulation
          simp [hs₂']
          sorry)
  have hsteps₂ :
    (fn'.semantics.guard
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep .τ
      s₂ (.yield op inputVals outputVals) _ := (Lts.WeakStep.single hstep₂).tail_non_tau
    (guard_single
      (by apply OpSpec.Guard.spec_yield)
      hstep₂')
  simp [hs₂'] at hsteps₂
  exact ⟨_, hsteps₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · simp
        sorry
      · simp
      · simp
        constructor
        and_intros;
        -- exact hwt'
        all_goals sorry
  ⟩

theorem sim_type_check_br
  [Arity Op]
  [InterpConsts V]
  [PCM T] [pcm : PCM.Lawful T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  {s₁ s₁' : Config Op χ V m n}
  {s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)}
  {l : Label Op V m n}
  {cond left right}
  (hsim : SimRel ioSpec s₁ s₂)
  (hret : s₁.cont = .expr (.br cond left right))
  (hstep : fn.semantics.lts.Step s₁ l s₁') :
    ∃ s₂',
      (fn'.semantics.guard
        ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep
        .τ s₂ l s₂' ∧
      SimRel ioSpec s₁' s₂'
  := by
  have ⟨hwt_fn, hdisj, _, hcont⟩ := hsim
  cases hstep with
  | step_init hexpr | step_tail hexpr
  | step_ret hexpr | step_op hexpr => simp [hret] at hexpr
  | step_br hexpr hget_cond hcond_bool =>
  have ⟨ctx, expr₂, hcont₂, hwt, hvars⟩ := hcont _ hexpr
  cases hwt with | wpt_br hwt₁ hwt₂ =>
  have hstep₂ :
    (fn'.semantics.guard
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.Step
      s₂ .τ _ :=
    guard_single
      .spec_tau
      (.step_br
        hcont₂
        (by
          simp [hvars]
          apply var_map_disjoint_union_get_var_left hget_cond)
        hcond_bool)
  exact ⟨_, .single hstep₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · simp
        sorry
      · simp
      · simp
        exists ctx
        constructor
        · split
          · exact hwt₁
          · exact hwt₂
        · sorry
  ⟩

/--
Type soundness theorem formulated as a simulation:
if the untyped `Fn` can execute without error, then
the typed version can also execute with the same trace
while keeping the ghost tokens disjoint, i.e., progress
is simulation and preservation is the `DisjointTokens`
invariant on the states.

Need to use weak simulation here due to `join` being
interpreted as silent steps.
-/
theorem sim_type_check
  {V T : Type u} -- TODO: relax this constraint
  [Arity Op]
  [InterpConsts V]
  [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [DecidableLE T]
  (opSpec : SimpleOpSpec Op T)
  (ioSpec : SimpleIOSpec T)
  (fn : Fn Op χ V m n)
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  (hwf : fn.AffineVar)
  (hwt : fn.WellPermTyped ioSpec fn') :
  fn.semantics ≲
    fn'.semantics.guard
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))
  := by
  apply Lts.Similarity.intro (SimRel ioSpec)
  constructor
  · apply sim_type_check_init hwt
  · intros s₁ s₂ l s₁' hsim hstep
    cases h₁ : s₁.cont with
    | init => exact sim_type_check_input hsim h₁ hstep
    | expr expr =>
      cases h₂ : expr <;> simp [h₂] at h₁
      case ret => exact sim_type_check_ret hsim h₁ hstep
      case tail => exact sim_type_check_tail hsim h₁ hstep
      case op => exact sim_type_check_op hsim h₁ hstep
      case br => exact sim_type_check_br hsim h₁ hstep

end Wavelet.Seq

/-
Proof sketch (for a single `Fn`):

We show that

```
fn.semantics
  ≲ᵣ fn'.semantics.guard
  ≲ᵣ (compileFn ... fn').semantics.guard ... (by fn'.semantics ≲ᵣ (compileFn ... fn').semantics)
  (... maybe some optimization passes)
```

Also for any `proc`
1. `proc.semantics.guard ...` is strongly confluent
2. `proc.semantics.guard P ≲ᵣ proc.semantics.guard P'`
   if `P → P'` (and in particular for trivial `P'`)
3. If we have a terminating trace in `proc.semantics.guard P`,
   then any trace in `proc.semantics` goes to the same final state.
-/
