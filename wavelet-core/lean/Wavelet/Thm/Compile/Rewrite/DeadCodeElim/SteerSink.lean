import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! `steer-sink`: a steer with a sunk output is two sinks. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

theorem steer_sink_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {flavor : Bool} {decider input output : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.steer flavor 1) [decider, input] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.sink 1) [output] []))
  (hne : i₂ ≠ i₁) :
    RuleOK proc [i₂, i₁] [.sink #v[input], .sink #v[decider]]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.sink 1) [output] [], .async (.steer flavor 1) [decider, input] [output]] := by
    simp [h₁, h₂]
  have hP' : ([.sink #v[input], .sink #v[decider]] : AtomicProcs Op χ V) =
      [.async (.sink 1) [input] [], .async (.sink 1) [decider] []] := by
    simp [AtomicProc.sink]
  -- Facts from affineness
  have hdi : decider ≠ input := by simpa using (haff.atom_nodup h₁).1
  have hdisj := (haff.atom_disjoint h₂ h₁ hne).1
  simp at hdisj
  obtain ⟨hod, hoi⟩ := hdisj
  -- `output` is no longer used after the rewrite; other channels are the same.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.sink #v[input], .sink #v[decider]] ∧
    (∀ y, y ≠ output → chans₀ y = chans₁ y) ∧
    chans₁ output = [], ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp [hP', Ne.symm hdi]
    · simp [hP']
    · simp [hP', hP]
    · simp [hP']
  · constructor
    · simp
    · -- `x` is read by the environment or the rest of the graph, so `x ≠ output`.
      rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, rfl, heq, hout⟩ hpop
      simp [hP] at hx
      have hxo : x ≠ output := hx.1
      refine ⟨λ y => if y = x then (chans₁ x).tail else chans₁ y, ?_, rfl, rfl, ?_, ?_⟩
      · intro y
        by_cases hy : y = x
        · subst hy
          have := hpop y
          rw [heq y hxo] at this
          simp [this]
        · simp [hy]
      · intro y hy
        have := hpop y
        by_cases hyx : y = x
        · subst hyx
          rw [heq y hy] at this
          simp [this]
        · simp [hyx] at this ⊢
          rw [← this, heq y hy]
      · simp [Ne.symm hxo, hout]
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, heq, hout⟩
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro y hy
        simp [heq y hy]
      · have : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
        simp [hout, ChanMap.pushed_not_mem this]
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _ ⟨rfl, rfl, heq, hout⟩ hget hinterp
        hlen₁ hlen₂ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        -- The sink of `output` fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hinterp.sink_inv
        obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen₁.symm
        refine ⟨_, _, .refl, ?_, rfl, ?_, hout⟩
        · simp
        · intro y hy
          have := hpop y
          simp [Ne.symm hy] at this
          simp [← this, heq y hy]
      | 1, hget =>
        -- The steer fires: sink both the decider and the input on the rewritten side.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, dv, xv, b, rfl, -, houts, hovals⟩ := hinterp.steer_inv hlen₁
        have hpushed : ∀ y, y ≠ output → ChanMap.pushed outputs outputVals y = [] := by
          intro y hy
          rw [houts, hovals]
          split <;> simp [Ne.symm hy]
        have hpop₁ := hpop decider
        have hpop₂ := hpop input
        simp [hdi, Ne.symm hdi] at hpop₁ hpop₂
        -- Sink the input, then the decider
        have hstep₁ := LocalTauStar.async_list_mem
          (L := ([.sink #v[input], .sink #v[decider]] : AtomicProcs Op χ V))
          (aop := .sink 1) (allInputs := [input]) (allOutputs := [])
          (inputs := [input]) (inputVals := [xv]) (outputs := []) (outputVals := [])
          (chans := chans₁)
          (chans' := λ y => if y = input then (chans₁ input).tail else chans₁ y)
          (by simp [AtomicProc.sink]) (.interp_sink rfl) rfl rfl
          (by
            intro y
            by_cases hy : y = input
            · subst hy
              rw [← heq y (Ne.symm hoi), hpop₂]
              simp
            · simp [Ne.symm hy, hy])
        have hstep₁ := hstep₁.eq_rhs rfl (by funext y; simp :
          _ = λ y => if y = input then (chans₁ input).tail else chans₁ y)
        have hstep₂ := LocalTauStar.async_list_mem
          (L := ([.sink #v[input], .sink #v[decider]] : AtomicProcs Op χ V))
          (aop := .sink 1) (allInputs := [decider]) (allOutputs := [])
          (inputs := [decider]) (inputVals := [dv]) (outputs := []) (outputVals := [])
          (chans := λ y => if y = input then (chans₁ input).tail else chans₁ y)
          (chans' := λ y => if y = decider then (chans₁ decider).tail
            else if y = input then (chans₁ input).tail else chans₁ y)
          (by simp [AtomicProc.sink]) (.interp_sink rfl) rfl rfl
          (by
            intro y
            by_cases hy : y = decider
            · subst hy
              have : chans₁ y = dv :: chans₀' y := by rw [← heq y (Ne.symm hod)]; exact hpop₁
              simp [hdi, this]
            · simp [Ne.symm hy, hy])
        refine ⟨_, _, hstep₁.trans hstep₂, ?_, rfl, ?_, ?_⟩
        · simp
        · intro y hy
          have := hpop y
          simp only [hpushed y hy, List.append_nil]
          by_cases hyd : y = decider
          · subst hyd
            simp [Ne.symm hdi] at this ⊢
            rw [heq y hy] at this
            simp [this]
          · by_cases hyi : y = input
            · subst hyi
              simp [Ne.symm hyd] at this ⊢
              rw [heq y hy] at this
              simp [this, hyd]
            · simp [Ne.symm hyd, Ne.symm hyi] at this
              simp [hyd, hyi, ← this, heq y hy]
        · simp [hod, hoi, hout]
  · rintro L₁ chans₁ ⟨_, rfl, heq, hout⟩
    refine ⟨rfl, ?_⟩
    funext y
    by_cases hy : y = output
    · subst hy; exact hout
    · exact (heq y hy).symm

end Wavelet.Compile.DeadCodeElim
