import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.UnusedChan

/-! `const-sink`: a constant into a sink is a sink. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

theorem const_sink_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {act output : χ} {v : V}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.const v 1) [act] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.sink 1) [output] []))
  (hne : i₂ ≠ i₁) :
    RuleOK proc [i₂, i₁] [.sink #v[act]]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.sink 1) [output] [], .async (.const v 1) [act] [output]] := by
    simp [h₁, h₂]
  have hP' : ([.sink #v[act]] : AtomicProcs Op χ V) = [.async (.sink 1) [act] []] := by
    simp [AtomicProc.sink]
  -- Facts from affineness
  have hao : act ≠ output := by simpa using (haff.atom_disjoint h₂ h₁ hne).1
  -- `output` is no longer used after the rewrite; other channels are the same.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.sink #v[act]] ∧
    UnusedChan.EqExcept output chans₀ chans₁, ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp [hP']
    · simp [hP']
    · simp [hP', hP]
    · simp [hP']
  · constructor
    · exact ⟨rfl, rfl, .empty⟩
    · -- `x` is read by the environment or the rest of the graph, so `x ≠ output`.
      rintro L₀ chans₀ L₁ chans₁ x w chans₀' hx _ ⟨rfl, rfl, hrel⟩ hpop
      simp [hP] at hx
      obtain ⟨chans₁', hpop₁, hrel'⟩ := hrel.pop hpop (by simp [Ne.symm hx.1])
      exact ⟨chans₁', hpop₁, rfl, rfl, hrel'⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, hrel⟩
      have : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
      exact ⟨rfl, rfl, hrel.frame_push this⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _ ⟨rfl, rfl, hrel⟩ hget hinterp
        hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        -- The sink of `output` fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hinterp.sink_inv
        obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hlen₁.symm
        refine ⟨_, _, .refl, ?_, rfl, ?_⟩
        · simp
        · simpa using hrel.pop_left hpop (λ y hy => by simp [Ne.symm hy])
      | 1, hget =>
        -- The constant fires: the rewritten sink consumes the same activation.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, ⟨a, av, ha, rfl⟩, rfl⟩ := hinterp.const_inv hlen₁
        obtain ⟨chans₁', hpop₁, hrel'⟩ :=
          hrel.pop hpop (ChanMap.pushed_not_mem (by simp [Ne.symm hao]))
        refine ⟨_, _, LocalTauStar.async_list_mem
          (aop := .sink 1) (allInputs := [act]) (allOutputs := [])
          (inputs := [act]) (outputs := []) (outputVals := [])
          (by simp [hP']) (.interp_sink rfl) rfl rfl hpop₁, ?_, rfl, ?_⟩
        · simp
        · exact hrel'.push (λ y hy => by simp [Ne.symm hy]) (by simp)
  · rintro L₁ chans₁ ⟨_, rfl, hrel⟩
    exact ⟨rfl, hrel.eq_empty⟩

end Wavelet.Compile.DeadCodeElim
