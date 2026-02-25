import Wavelet.Data.Basic
import Wavelet.Dataflow.Proc

namespace Wavelet.Dataflow

open Semantics

/-- Each channel name is used at most once. -/
def AtomicProcs.AffineChan [Arity Op] (aps : AtomicProcs Op χ V) : Prop
  :=
  (∀ ap ∈ aps, ap.inputs.Nodup ∧ ap.outputs.Nodup) ∧
  aps.Pairwise (λ ap₁ ap₂ =>
    ap₁.inputs.Disjoint ap₂.inputs ∧ ap₁.outputs.Disjoint ap₂.outputs)

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
  := aps.forM λ ap => do
    ap.checkNoDupIO.mapError λ err =>
      s!"atomic proc has duplicate IO: {err}"

/-- Executable version of `AtomicProcs.AffineChan`. -/
def AtomicProcs.checkAffineChan [Arity Op] [DecidableEq χ] [Repr χ]
  (aps : AtomicProcs Op χ V) : Except String Unit
  := do
  aps.checkNoDupIO
  (List.finRange aps.length).forM λ i => do
    (List.finRange aps.length).forM λ j => do
      if i < j then
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
    ∀ ap ∈ aps, ap.inputs.Nodup ∧ ap.outputs.Nodup
  := by
  simp only [AtomicProcs.checkNoDupIO, List.forM_ok_iff_all_ok]
  simp [← AtomicProc.checkNoDupIO.correct]

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
      simp [List.pairwise_iff_getElem]
      intros i j hi hj hlt
      specialize h ⟨i, hi⟩ (List.mem_finRange _) ⟨j, hj⟩ (List.mem_finRange _)
      simp [hlt] at h
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
      split
      · rename_i h₂
        have := (List.pairwise_iff_getElem.mp h.2) i j (by simp) (by simp) h₂
        simp at this
        simp [this, pure, Except.pure, Except.isOk, Except.toBool]
      · rfl

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
  if hlt : i < j then
    have ⟨_, _, hatoms, _, _⟩ := haff
    exact ((List.pairwise_iff_getElem.mp hatoms.2) i j (by simp) (by simp) hlt).1
  else
    have ⟨_, _, hatoms, _, _⟩ := haff
    have hlt : j < i := by omega
    have := ((List.pairwise_iff_getElem.mp hatoms.2) j i (by simp) (by simp) hlt).1
    exact this.symm

theorem Proc.AffineChan.atom_outputs_disjoint
  [Arity Op]
  {proc : Proc Op χ V m n}
  (haff : proc.AffineChan)
  (i j : Fin proc.atoms.length)
  (hne : i ≠ j) :
    proc.atoms[i].outputs.Disjoint proc.atoms[j].outputs
  := by
  if hlt : i < j then
    have ⟨_, _, hatoms, _, _⟩ := haff
    exact ((List.pairwise_iff_getElem.mp hatoms.2) i j (by simp) (by simp) hlt).2
  else
    have ⟨_, _, hatoms, _, _⟩ := haff
    have hlt : j < i := by omega
    have := ((List.pairwise_iff_getElem.mp hatoms.2) j i (by simp) (by simp) hlt).2
    exact this.symm

theorem Proc.AffineChan.getElem_nodup
  [Arity Op]
  {proc : Proc Op χ V m n}
  (haff : proc.AffineChan)
  (i : Fin proc.atoms.length) :
    proc.atoms[i].inputs.Nodup ∧ proc.atoms[i].outputs.Nodup
  := by
  have ⟨_, _, hatoms, _, _⟩ := haff
  apply hatoms.1
  simp

end Wavelet.Dataflow
