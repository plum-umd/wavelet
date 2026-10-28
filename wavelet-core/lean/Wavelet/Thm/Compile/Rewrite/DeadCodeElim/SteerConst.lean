import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ConstLemmas

/-! `steer-const-*`: a steer whose decider is a constant. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow ConstLemmas

theorem steer_const_true_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ : Nat}
  {flavor : Bool} {decider input output : χ} {v : V}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.steer flavor 1) [decider, input] [output]))
  (hconst : FromConst proc.atoms decider v)
  (hbool : InterpConsts.toBool v = some flavor) :
    RuleOK proc [i₁] [.order #v[input, decider] output]
  := by
  have hP : matchedOf proc.atoms [i₁] = [.async (.steer flavor 1) [decider, input] [output]] := by
    simp [h₁]
  have hP' : ([.order #v[input, decider] output] : AtomicProcs Op χ V) =
      [.async (.order 2) [input, decider] [output]] := by
    simp [AtomicProc.order]
  have hdi : decider ≠ input := by simpa using (haff.atom_nodup h₁).1
  -- The steer always passes, so it behaves like the order: same channels on both sides.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₁] ∧
    L₁ = [.async (.order 2) [input, decider] [output]] ∧
    chans₀ = chans₁, ?_, ?_⟩
  · constructor
    · simp
    · simp [(List.getElem?_eq_some_iff.mp h₁).1]
    · simp [hP', Ne.symm hdi]
    · simp [hP']
    · simp [hP', hP]
    · simp [hP', hP]
  · constructor
    · exact ⟨rfl, hP', rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ x w chans₀' _ _ ⟨rfl, rfl, rfl⟩ hpop
      exact ⟨_, hpop, rfl, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ _ _ _ ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, rfl⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' hinv _ ⟨rfl, rfl, rfl⟩ hget hinterp
        hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, dv, xv, b, rfl, hb, houts, hovals⟩ := hinterp.steer_inv hlen₁
        -- The decider is always `v`, so the steer passes.
        have hpd := hpop decider
        simp [Ne.symm hdi] at hpd
        have hdv : dv = v := hconst.eq_of_mem hinv dv (by simp [hpd])
        rw [hdv, hbool] at hb
        have hbf : b = flavor := (Option.some.inj hb).symm
        rw [if_pos hbf] at houts hovals
        subst houts hovals
        refine ⟨_, _, LocalTauStar.async_list_mem
          (aop := .order 2) (allInputs := [input, decider]) (allOutputs := [output])
          (inputs := [input, decider]) (inputVals := [xv, dv]) (outputs := [output])
          (outputVals := [xv]) (chans' := chans₀')
          (by simp) (AsyncOp.Interp.order_mk rfl rfl) rfl rfl ?_, ?_, rfl, rfl⟩
        · intro y
          rw [hpop y, ChanMap.pushed_swap hdi]
        · simp
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨hP'.symm, rfl⟩

theorem steer_const_false_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ : Nat}
  {flavor b : Bool} {decider input output : χ} {v : V}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.steer flavor 1) [decider, input] [output]))
  (hconst : FromConst proc.atoms decider v)
  (hbool : InterpConsts.toBool v = some b)
  (hne : b ≠ flavor) :
    RuleOK proc [i₁] [
      .sink #v[input],
      .sink #v[decider],
      .inact #v[output],
    ]
  := by
  have hP : matchedOf proc.atoms [i₁] = [.async (.steer flavor 1) [decider, input] [output]] := by
    simp [h₁]
  have hP' : ([.sink #v[input], .sink #v[decider], .inact #v[output]] : AtomicProcs Op χ V) =
      [.async (.sink 1) [input] [], .async (.sink 1) [decider] [], .async (.inact 1) [] [output]] := by
    simp [AtomicProc.sink, AtomicProc.inact]
  have hdi : decider ≠ input := by simpa using (haff.atom_nodup h₁).1
  -- The steer never passes, so it behaves like two sinks: same channels on both sides.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₁] ∧
    L₁ = [.async (.sink 1) [input] [], .async (.sink 1) [decider] [], .async (.inact 1) [] [output]] ∧
    chans₀ = chans₁, ?_, ?_⟩
  · constructor
    · simp
    · simp [(List.getElem?_eq_some_iff.mp h₁).1]
    · simp [hP', Ne.symm hdi]
    · simp [hP']
    · simp [hP', hP]
    · simp [hP', hP]
  · constructor
    · exact ⟨rfl, hP', rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ x w chans₀' _ _ ⟨rfl, rfl, rfl⟩ hpop
      exact ⟨_, hpop, rfl, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ _ _ _ ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, rfl⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' hinv _ ⟨rfl, rfl, rfl⟩ hget hinterp
        hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, dv, xv, b', rfl, hb', houts, hovals⟩ := hinterp.steer_inv hlen₁
        -- The decider is always `v`, so the steer does not pass.
        have hpd := hpop decider
        have hpi := hpop input
        simp [hdi, Ne.symm hdi] at hpd hpi
        have hdv : dv = v := hconst.eq_of_mem hinv dv (by simp [hpd])
        rw [hdv, hbool] at hb'
        have hbf : ¬ b' = flavor := (Option.some.inj hb') ▸ hne
        rw [if_neg hbf] at houts hovals
        subst houts hovals
        -- Sink the input, then the decider.
        obtain ⟨chans₁, hpop₁, hi₁, hne₁⟩ := ChanMap.pop_one hpi
        obtain ⟨chans₂, hpop₂, hd₂, hne₂⟩ := ChanMap.pop_one
          (chans := chans₁) (x := decider) (by rw [hne₁ _ hdi, hpd])
        have hstep₁ := LocalTauStar.async_list_mem
          (L := ([.async (.sink 1) [input] [], .async (.sink 1) [decider] [],
            .async (.inact 1) [] [output]] : AtomicProcs Op χ V))
          (aop := .sink 1) (allInputs := [input]) (allOutputs := [])
          (inputs := [input]) (outputs := []) (outputVals := [])
          (by simp) (.interp_sink rfl) rfl rfl hpop₁
        have hstep₂ := LocalTauStar.async_list_mem
          (L := ([.async (.sink 1) [input] [], .async (.sink 1) [decider] [],
            .async (.inact 1) [] [output]] : AtomicProcs Op χ V))
          (aop := .sink 1) (allInputs := [decider]) (allOutputs := [])
          (inputs := [decider]) (outputs := []) (outputVals := [])
          (by simp) (.interp_sink rfl) rfl rfl hpop₂
        refine ⟨_, _, (hstep₁.eq_rhs rfl (funext λ y => by simp)).trans hstep₂, ?_, rfl, ?_⟩
        · simp
        · funext y
          simp only [ChanMap.pushed_nil_left, List.append_nil]
          by_cases hyd : y = decider
          · subst hyd; rw [hd₂]
          · by_cases hyi : y = input
            · subst hyi; rw [hne₂ _ hyd, hi₁]
            · have := hpop y
              simp [Ne.symm hyd, Ne.symm hyi] at this
              rw [hne₂ _ hyd, hne₁ _ hyi, this]
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨hP'.symm, rfl⟩

end Wavelet.Compile.DeadCodeElim
