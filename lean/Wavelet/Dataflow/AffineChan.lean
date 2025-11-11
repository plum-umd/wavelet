import Batteries.Data.Char.Basic

import Wavelet.Data.List
import Wavelet.Data.Except

import Wavelet.Dataflow.Proc

namespace Wavelet.Dataflow

open Semantics

/-- Each channel name is used at most once. -/
def AtomicProcs.AffineChan [Arity Op] (aps : AtomicProcs Op χ V) : Prop
  :=
  (∀ (i : Fin aps.length),
    aps[i].inputs.Nodup ∧ aps[i].outputs.Nodup) ∧
  (∀ (i j : Fin aps.length), i ≠ j →
    aps[i].inputs.Disjoint aps[j].inputs ∧
    aps[i].outputs.Disjoint aps[j].outputs)

/-- Each channel name is used at most once. -/
def Proc.AffineChan [Arity Op] (proc : Proc Op χ V m n) : Prop :=
  proc.inputs.toList.Nodup ∧
  proc.outputs.toList.Nodup ∧
  proc.atoms.AffineChan ∧
  (∀ ap ∈ proc.atoms, ap.outputs.Disjoint proc.inputs.toList) ∧
  (∀ ap ∈ proc.atoms, ap.inputs.Disjoint proc.outputs.toList)

/-- Helper function to check that the atom has duplicate intputs or outputs. -/
def AtomicProc.checkNoDupIO [Arity Op] [DecidableEq χ]
  (ap : AtomicProc Op χ V) : Except String Unit
  := do
  if ¬ ap.inputs.Nodup then
    throw s!"duplicate inputs"
  if ¬ ap.outputs.Nodup then
    throw s!"duplicate outputs"

/-- Helper function to check that no atom has duplicate intputs or outputs. -/
def AtomicProcs.checkNoDupIO [Arity Op] [DecidableEq χ]
  (aps : AtomicProcs Op χ V) : Except String Unit
  := (List.finRange aps.length).forM λ i => do
    aps[i].checkNoDupIO.mapError λ err =>
      s!"atomic proc {i}: {err}"

/-- Executable version of `AtomicProcs.AffineChan`. -/
def AtomicProcs.checkAffineChan [Arity Op] [DecidableEq χ] [Repr χ]
  (aps : AtomicProcs Op χ V) : Except String Unit
  := do
  aps.checkNoDupIO
  (List.finRange aps.length).forM λ i => do
    (List.finRange aps.length).forM λ j => do
      if i ≠ j then
        if ¬ aps[i].inputs.Disjoint aps[j].inputs then
          throw s!"atomic procs {i} and {j} have overlapping inputs"
        if ¬ aps[i].outputs.Disjoint aps[j].outputs then
          throw s!"atomic procs {i} and {j} have overlapping outputs"

/-- Executable version of `Proc.AffineChan`. -/
def Proc.checkAffineChan [Arity Op] [DecidableEq χ] [Repr χ]
  (proc : Proc Op χ V m n) : Except String Unit
  := do
  if ¬ proc.inputs.toList.Nodup then
    throw s!"proc has duplicate inputs"
  if ¬ proc.outputs.toList.Nodup then
    throw s!"proc has duplicate outputs"
  proc.atoms.checkAffineChan
  (List.finRange proc.atoms.length).forM λ i => do
    if ¬ proc.atoms[i].outputs.Disjoint proc.inputs.toList then
      throw s!"atomic proc {i} outputs overlap with global inputs"
    if ¬ proc.atoms[i].inputs.Disjoint proc.outputs.toList then
      throw s!"atomic proc {i} inputs overlap with global outputs"

theorem AtomicProc.checkNoDupIO.correct
  [Arity Op] [DecidableEq χ]
  {ap : AtomicProc Op χ V} :
    ap.checkNoDupIO.isOk ↔ ap.inputs.Nodup ∧ ap.outputs.Nodup
  := by
  constructor
  · intros hok
    simp [AtomicProc.checkNoDupIO] at hok
    split at hok <;> rename_i h₁
    · split at hok <;> rename_i h₂
      · exact ⟨h₁, h₂⟩
      · contradiction
    · contradiction
  · intros h
    simp [AtomicProc.checkNoDupIO, h]
    rfl

theorem AtomicProcs.checkNoDupIO.correct
  [Arity Op] [DecidableEq χ]
  {aps : AtomicProcs Op χ V} :
    aps.checkNoDupIO.isOk ↔
    ∀ (i : Fin aps.length), aps[i].inputs.Nodup ∧ aps[i].outputs.Nodup
  := by
  simp only [AtomicProcs.checkNoDupIO, List.forM_ok_iff_all_ok]
  simp [← AtomicProc.checkNoDupIO.correct]
  grind only [List.mem_finRange, =_ List.contains_iff_mem, cases Or]

theorem AtomicProcs.checkAffineChan.correct
  [Arity Op] [DecidableEq χ] [Repr χ]
  {aps : AtomicProcs Op χ V} :
    aps.checkAffineChan.isOk ↔ aps.AffineChan
  := by
  constructor
  · intros h
    simp [AtomicProcs.checkAffineChan, bind, Except.bind] at h
    split at h; contradiction
    rename_i h₁
    constructor
    · apply AtomicProcs.checkNoDupIO.correct.mp
      simp [h₁, Except.isOk, Except.toBool]
    · simp only [forM, List.forM_ok_iff_all_ok] at h
      intros i j hne
      specialize h i (List.mem_finRange _) j (List.mem_finRange _)
      simp [hne] at h
      split at h
      any_goals contradiction
      rename_i h₂
      simp [pure, Except.pure] at h
      split at h
      any_goals contradiction
      rename_i h₃
      exact ⟨h₂, h₃⟩
  · intros h
    simp [AtomicProcs.checkAffineChan, bind, Except.bind]
    split <;> rename_i h₁
    · have := AtomicProcs.checkNoDupIO.correct.mpr h.1
      simp [h₁, Except.isOk, Except.toBool] at this
    · simp only [forM, List.forM_ok_iff_all_ok]
      intros i _ j _
      split; rfl
      rename_i h₂
      have := h.2 i j h₂
      simp at this
      simp [this, pure, Except.pure, Except.isOk, Except.toBool]

theorem Proc.checkAffineChan.correct
  [Arity Op] [DecidableEq χ] [Repr χ]
  {proc : Proc Op χ V m n} :
    proc.checkAffineChan.isOk ↔ proc.AffineChan
  := by
  constructor
  · intros h
    simp [Proc.AffineChan]
    simp [Proc.checkAffineChan, bind, Except.bind] at h
    split at h; any_goals contradiction
    rename_i h₁; simp [h₁]
    simp [pure, Except.pure] at h
    split at h; any_goals contradiction
    rename_i h₂; simp [h₂]
    split at h; any_goals contradiction
    rename_i h₃
    simp [AtomicProcs.checkAffineChan.correct.mp (by rw [h₃, Except.isOk, Except.toBool])]
    simp only [forM, List.forM_ok_iff_all_ok] at h
    constructor
    · intros ap hmem
      have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
      specialize h ⟨i, hi⟩ (List.mem_finRange _)
      split at h; any_goals contradiction
      rename_i h₄
      simp [hget_i] at h₄
      exact h₄
    · intros ap hmem
      have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
      specialize h ⟨i, hi⟩ (List.mem_finRange _)
      split at h; any_goals contradiction
      split at h; any_goals contradiction
      rename_i h₅
      simp [hget_i] at h₅
      exact h₅
  · intros h
    have ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    simp [Proc.checkAffineChan, bind, Except.bind, h₁, h₂,
      pure, Except.pure]
    have := AtomicProcs.checkAffineChan.correct.mpr h₃
    split <;> rename_i h₆
    · simp [h₆, Except.isOk, Except.toBool] at this
    · simp only [forM, List.forM_ok_iff_all_ok]
      intros i _
      specialize h₄ proc.atoms[i] (by simp)
      specialize h₅ proc.atoms[i] (by simp)
      simp at h₄ h₅
      simp [h₄, h₅, Except.isOk, Except.toBool]

instance [Arity Op] [DecidableEq χ] [Repr χ]
  {proc : Proc Op χ V m n} :
  Decidable (proc.AffineChan) :=
  if h : proc.checkAffineChan.isOk then
    isTrue (Proc.checkAffineChan.correct.mp h)
  else
    isFalse (by
      intros h
      have := Proc.checkAffineChan.correct.mpr h
      contradiction)

theorem Proc.AffineChan.atom_inputs_disjoint
  [Arity Op]
  {proc : Proc Op χ V m n}
  (haff : proc.AffineChan)
  (i j : Fin proc.atoms.length)
  (hne : i ≠ j) :
    proc.atoms[i].inputs.Disjoint proc.atoms[j].inputs
  := by
  have ⟨_, _, hatoms, _, _⟩ := haff
  exact (hatoms.2 i j hne).1

theorem Proc.AffineChan.atom_outputs_disjoint
  [Arity Op]
  {proc : Proc Op χ V m n}
  (haff : proc.AffineChan)
  (i j : Fin proc.atoms.length)
  (hne : i ≠ j) :
    proc.atoms[i].outputs.Disjoint proc.atoms[j].outputs
  := by
  have ⟨_, _, hatoms, _, _⟩ := haff
  exact (hatoms.2 i j hne).2

/-- `AffineChan` is a state invariant. -/
theorem Proc.AffineChan.inv
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {s : Config Op χ V m n}
  (haff : s.proc.AffineChan) :
    Config.Step.IsInvariantAt (·.proc.AffineChan) s
  := by
  apply Lts.IsInvariantAt.by_induction
  · exact haff
  · intros s₁ s₂ l hinv hstep
    cases hstep with
    | step_async _ hget hinterp _ =>
      rename Nat => i
      simp [Proc.AffineChan]
      have ⟨h₁, h₂, ⟨h₃₁, h₃₂⟩, h₄, h₅⟩ := hinv
      simp [h₁, h₂]
      and_intros
      · intros j
        rcases j with ⟨j, hlt⟩
        simp at hlt
        by_cases h₁ : i = j
        · subst h₁
          have := h₃₁ ⟨i, by omega⟩
          simp [AtomicProc.inputs, AtomicProc.outputs, hget] at this ⊢
          exact this
        · simp [h₁]
          apply h₃₁ ⟨j, hlt⟩
      · intros j k hne
        rcases j with ⟨j, hj⟩
        rcases k with ⟨k, hk⟩
        simp at hj hk hne
        have := h₃₂ ⟨j, hj⟩ ⟨k, hk⟩ (by simp [hne])
        simp at this
        grind [AtomicProc.inputs, AtomicProc.outputs]
      · intros ap hmem_ap
        have := List.mem_or_eq_of_mem_set hmem_ap
        cases this with
        | inl hmem_ap =>
          exact h₄ ap hmem_ap
        | inr heq_ap =>
          subst heq_ap
          have := h₄ _ (List.mem_of_getElem hget)
          exact this
      · intros ap hmem_ap
        have := List.mem_or_eq_of_mem_set hmem_ap
        cases this with
        | inl hmem_ap =>
          exact h₅ ap hmem_ap
        | inr heq_ap =>
          subst heq_ap
          have := h₅ _ (List.mem_of_getElem hget)
          exact this
    | _ => simp [hinv]

end Wavelet.Dataflow
