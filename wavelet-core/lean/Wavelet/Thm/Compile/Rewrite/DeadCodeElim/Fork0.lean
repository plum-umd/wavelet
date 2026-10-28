import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! `fork-0`: a fork with no outputs is a sink. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

theorem fork_0_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ : Nat}
  {input : χ}
  (h₁ : proc.atoms[i₁]? = some (.async (.fork 0) [input] [])) :
    RuleOK proc [i₁] [.sink [input].toVector]
  := by
  have hP : matchedOf proc.atoms [i₁] = [.async (.fork 0) [input] []] := by
    simp [h₁]
  have hP' : ([.sink [input].toVector] : AtomicProcs Op χ V) =
      [.async (.sink 1) [input] []] := by
    simp [AtomicProc.sink, List.toVector]
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = [.async (.fork 0) [input] []] ∧
    L₁ = [.sink [input].toVector] ∧
    chans₀ = chans₁, ?_, ?_⟩
  · constructor
    · simp
    · simp [(List.getElem?_eq_some_iff.mp h₁).1]
    · simp [hP']
    · simp [hP']
    · simp [hP, hP']
    · simp [hP']
  · constructor
    · simp [hP]
    · rintro L₀ chans₀ L₁ chans₁ x v chans₀' _ _ ⟨rfl, rfl, rfl⟩ hpop
      exact ⟨_, hpop, rfl, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ _ _ _ ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, rfl⟩ hmem
      simp at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _ ⟨rfl, rfl, rfl⟩ hget hinterp
        hlen₁ _ hpop
      have hi : i = 0 := by
        rcases i with _ | i
        · rfl
        · simp at hget
      subst hi
      simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, rfl⟩ := hget
      -- The fork consumes its input without outputs, as the sink does.
      obtain ⟨rfl, rfl, rfl, -, v, rfl, -, rfl⟩ := hinterp.fork_inv hlen₁
      refine ⟨_, _, LocalTauStar.async_list_mem
        (aop := .sink 1) (allInputs := [input]) (allOutputs := [])
        (inputs := [input]) (outputs := []) (outputVals := [])
        (by simp [hP']) (.interp_sink rfl) rfl rfl hpop, ?_, rfl, ?_⟩
      · simp
      · simp
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end Wavelet.Compile.DeadCodeElim
