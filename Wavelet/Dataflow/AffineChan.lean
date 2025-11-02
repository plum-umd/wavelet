import Wavelet.Dataflow.Proc

namespace Wavelet.Dataflow

open Semantics

def AtomicProc.inputs [Arity Op] : AtomicProc Op χ V → List χ
  | .op _ inputs _ => inputs.toList
  | .async _ inputs _ => inputs

def AtomicProc.outputs [Arity Op] : AtomicProc Op χ V → List χ
  | .op _ _ outputs => outputs.toList
  | .async _ _ outputs => outputs

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
