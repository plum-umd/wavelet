import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.UnusedChan

/-! `switch-sink-*`: a switch with one output sunk is a steer. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

/-- A switch with the output `sunk` sunk is a steer to the other output `kept`. -/
private theorem switch_sink_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {flavor : Bool} {decider input output₁ output₂ kept sunk : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.switch 1) [decider, input] [output₁, output₂]))
  (h₂ : proc.atoms[i₂]? = some (.async (.sink 1) [sunk] []))
  (hne : i₂ ≠ i₁)
  (hkept : kept = output₁ ∨ kept = output₂)
  (hsunk : sunk = output₁ ∨ sunk = output₂)
  (hks : kept ≠ sunk)
  (hout : ∀ b : Bool,
    (if b then [output₁] else [output₂]) = if b = flavor then [kept] else [sunk]) :
    RuleOK proc [i₂, i₁] [.steer flavor decider #v[input] #v[kept]]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.sink 1) [sunk] [], .async (.switch 1) [decider, input] [output₁, output₂]] := by
    simp [h₁, h₂]
  have hP' : ([.steer flavor decider #v[input] #v[kept]] : AtomicProcs Op χ V) =
      [.async (.steer flavor 1) [decider, input] [kept]] := by
    simp [AtomicProc.steer]
  -- Facts from affineness
  have hdi : decider ≠ input := by simpa using (haff.atom_nodup h₁).1
  have hdisj := (haff.atom_disjoint h₂ h₁ hne).1
  simp at hdisj
  obtain ⟨hsd, hsi⟩ := hdisj
  -- `sunk` is no longer used after the rewrite; other channels are the same.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.steer flavor decider #v[input] #v[kept]] ∧
    UnusedChan.EqExcept sunk chans₀ chans₁, ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp [hP', hdi]
    · simp [hP']
    · simp [hP', hP]
    · simp [hP', hP, hkept]
  · constructor
    · exact ⟨rfl, rfl, .empty⟩
    · -- `x` is read by the environment or the rest of the graph, so `x ≠ sunk`.
      rintro L₀ chans₀ L₁ chans₁ x w chans₀' hx _ ⟨rfl, rfl, hrel⟩ hpop
      simp [hP] at hx
      obtain ⟨chans₁', hpop₁, hrel'⟩ := hrel.pop hpop (by simp [Ne.symm hx.1])
      exact ⟨chans₁', hpop₁, rfl, rfl, hrel'⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, hrel⟩
      have : sunk ∉ outs := λ h => by
        have := (hx sunk h).1
        rcases hsunk with rfl | rfl <;> simp [hP] at this
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
        -- The sink of `sunk` fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hinterp.sink_inv
        obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hlen₁.symm
        refine ⟨_, _, .refl, ?_, rfl, ?_⟩
        · simp
        · simpa using hrel.pop_left hpop (λ y hy => by simp [Ne.symm hy])
      | 1, hget =>
        -- The switch fires: the steer reads the same values.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, dv, xv, b, rfl, hb, houts, rfl⟩ := hinterp.switch_inv hlen₁
        rw [hout b] at houts
        subst houts
        obtain ⟨chans₁', hpop₁, hrel'⟩ :=
          hrel.pop hpop (ChanMap.pushed_not_mem (by simp [hsd, hsi]))
        by_cases hbf : b = flavor
        · -- The switch writes to `kept`, and the steer passes.
          refine ⟨_, _, LocalTauStar.async_list_mem
            (aop := .steer flavor 1) (allInputs := [decider, input]) (allOutputs := [kept])
            (inputs := [decider, input]) (outputs := [kept]) (outputVals := [xv])
            (by simp [hP']) (.interp_steer_true (k := 1) rfl rfl hb hbf) rfl rfl hpop₁,
            ?_, rfl, ?_⟩
          · simp
          · rw [if_pos hbf]
            exact hrel'.push (λ _ _ => rfl) (ChanMap.pushed_not_mem (by simp [Ne.symm hks]))
        · -- The switch writes to `sunk`, and the steer drops.
          refine ⟨_, _, LocalTauStar.async_list_mem
            (aop := .steer flavor 1) (allInputs := [decider, input]) (allOutputs := [kept])
            (inputs := [decider, input]) (outputs := []) (outputVals := [])
            (by simp [hP']) (.interp_steer_false (k := 1) rfl rfl hb hbf) rfl rfl hpop₁,
            ?_, rfl, ?_⟩
          · simp
          · rw [if_neg hbf]
            exact hrel'.push (λ y hy => by simp [Ne.symm hy]) (by simp)
  · rintro L₁ chans₁ ⟨_, rfl, hrel⟩
    exact ⟨rfl, hrel.eq_empty⟩

theorem switch_sink_left_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {decider input output₁ output₂ : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.switch 1) [decider, input] [output₁, output₂]))
  (h₂ : proc.atoms[i₂]? = some (.async (.sink 1) [output₁] []))
  (hne : i₂ ≠ i₁) :
    RuleOK proc [i₂, i₁] [.steer false decider #v[input] #v[output₂]]
  := by
  have hne' : output₁ ≠ output₂ := by simpa using (haff.atom_nodup h₁).2
  exact switch_sink_ok haff h₁ h₂ hne (.inr rfl) (.inl rfl) (Ne.symm hne')
    (by intro b; cases b <;> simp)

theorem switch_sink_right_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {decider input output₁ output₂ : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.switch 1) [decider, input] [output₁, output₂]))
  (h₂ : proc.atoms[i₂]? = some (.async (.sink 1) [output₂] []))
  (hne : i₂ ≠ i₁)
  (hne' : output₁ ≠ output₂) :
    RuleOK proc [i₂, i₁] [.steer true decider #v[input] #v[output₁]]
  := switch_sink_ok haff h₁ h₂ hne (.inl rfl) (.inr rfl) hne'
    (by intro b; cases b <;> simp)

end Wavelet.Compile.DeadCodeElim
