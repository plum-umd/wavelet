import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! `order-1`: an order with one input is a forward. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

theorem order_1_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ : Nat}
  {input output : χ}
  (h₁ : proc.atoms[i₁]? = some (.async (.order 1) [input] [output])) :
    RuleOK proc [i₁] [.forward #v[input] #v[output]]
  := by
  have hP : matchedOf proc.atoms [i₁] = [.async (.order 1) [input] [output]] := by
    simp [h₁]
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = [.async (.order 1) [input] [output]] ∧
    L₁ = [.forward #v[input] #v[output]] ∧
    chans₀ = chans₁, ?_, ?_⟩
  · constructor
    · simp
    · simp [(List.getElem?_eq_some_iff.mp h₁).1]
    · simp [AtomicProc.forward]
    · simp [AtomicProc.forward]
    · simp [hP, AtomicProc.forward]
    · simp [hP, AtomicProc.forward]
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
      -- The order passes its only input, as the forward does.
      obtain ⟨rfl, rfl, rfl, -, v, rest, rfl, rfl⟩ := hinterp.order_inv
      obtain rfl : rest = [] := by simpa using hlen₁
      refine ⟨_, _, LocalTauStar.async_list_mem
        (aop := .forward 1) (allInputs := [input]) (allOutputs := [output])
        (inputs := [input]) (outputs := [output])
        (by simp [AtomicProc.forward])
        (.interp_forward (k := 1) rfl rfl) rfl rfl hpop, ?_, rfl, ?_⟩
      · simp
      · simp
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end Wavelet.Compile.DeadCodeElim
