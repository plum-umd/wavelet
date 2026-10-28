import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ConstLemmas

/-! `carry-false`/`carry-true`: a carry with a constant decider is a forward. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow ConstLemmas

theorem carry_false_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ : Nat}
  {decider inputL inputR output : χ} {v : V}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .popLeft 1) [decider, inputL, inputR] [output]))
  (hconst : FromConst proc.atoms decider v)
  (hbool : InterpConsts.toBool v = some false) :
    RuleOK proc [i₁] [
      .forward #v[inputL] #v[output],
      .sink #v[decider],
      .sink #v[inputR],
    ]
  := by
  have hP : matchedOf proc.atoms [i₁] =
      [.async (.merge .popLeft 1) [decider, inputL, inputR] [output]] := by
    simp [h₁]
  have hP' : ([.forward #v[inputL] #v[output], .sink #v[decider], .sink #v[inputR]] :
      AtomicProcs Op χ V) =
      [.async (.forward 1) [inputL] [output], .async (.sink 1) [decider] [],
        .async (.sink 1) [inputR] []] := by
    simp [AtomicProc.forward, AtomicProc.sink]
  have hnd := (haff.atom_nodup h₁).1
  simp at hnd
  obtain ⟨⟨hdl, hdr⟩, hlr⟩ := hnd
  -- The carry alternates between `popLeft` and `decider` (always false);
  -- `inputR` is never read. Same channels on both sides.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    (L₀ = [.async (.merge .popLeft 1) [decider, inputL, inputR] [output]] ∨
      L₀ = [.async (.merge .decider 1) [decider, inputL, inputR] [output]]) ∧
    L₁ = [.async (.forward 1) [inputL] [output], .async (.sink 1) [decider] [],
      .async (.sink 1) [inputR] []] ∧
    chans₀ = chans₁, ?_, ?_⟩
  · constructor
    · simp
    · simp [(List.getElem?_eq_some_iff.mp h₁).1]
    · simp [hP', Ne.symm hdl, hlr, hdr]
    · simp [hP']
    · simp [hP', hP]
    · simp [hP', hP]
  · constructor
    · exact ⟨.inl hP, hP', rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ x w chans₀' _ _ ⟨hL₀, rfl, rfl⟩ hpop
      exact ⟨_, hpop, hL₀, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ _ _ _ ⟨hL₀, rfl, rfl⟩
      exact ⟨hL₀, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨hL₀, rfl, rfl⟩ hmem
      rcases hL₀ with rfl | rfl <;> simp at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' hinv _ ⟨hL₀, rfl, rfl⟩ hget hinterp
        hlen₁ _ hpop
      obtain ⟨st, hst, rfl⟩ : ∃ st, (st = .popLeft ∨ st = .decider) ∧
          L₀ = [.async (.merge st 1) [decider, inputL, inputR] [output]] := by
        rcases hL₀ with rfl | rfl
        · exact ⟨_, .inl rfl, rfl⟩
        · exact ⟨_, .inr rfl, rfl⟩
      match i, hget with
      | 0, hget =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        rcases hinterp.merge_inv hlen₁ with
          ⟨rfl, rfl, rfl, rfl, w, rfl, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, rfl, rfl, rfl, dv, b, rfl, hb, rfl⟩
        · -- `popLeft`: the forward fires.
          refine ⟨_, _, LocalTauStar.async_list_mem
            (aop := .forward 1) (allInputs := [inputL]) (allOutputs := [output])
            (inputs := [inputL]) (outputs := [output])
            (by simp) (.interp_forward rfl rfl) rfl rfl hpop, .inr (by simp), rfl, rfl⟩
        · -- `popRight` is unreachable.
          simp at hst
        · -- `decider`: the decider is always false, so the sink of `decider` fires.
          have hpd := hpop decider
          simp at hpd
          have hdv : dv = v := hconst.eq_of_mem hinv dv (by simp [hpd])
          rw [hdv, hbool] at hb
          obtain rfl : b = false := (Option.some.inj hb).symm
          refine ⟨_, _, LocalTauStar.async_list_mem
            (aop := .sink 1) (allInputs := [decider]) (allOutputs := [])
            (inputs := [decider]) (outputs := []) (outputVals := [])
            (by simp) (.interp_sink rfl) rfl rfl hpop, .inl (by simp), rfl, rfl⟩
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨hP'.symm, rfl⟩

theorem carry_true_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ : Nat}
  {decider inputL inputR output : χ} {v : V}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .popRight 1) [decider, inputL, inputR] [output]))
  (hconst : FromConst proc.atoms decider v)
  (hbool : InterpConsts.toBool v = some true) :
    RuleOK proc [i₁] [
      .forward #v[inputR] #v[output],
      .sink #v[decider],
      .sink #v[inputL],
    ]
  := by
  have hP : matchedOf proc.atoms [i₁] =
      [.async (.merge .popRight 1) [decider, inputL, inputR] [output]] := by
    simp [h₁]
  have hP' : ([.forward #v[inputR] #v[output], .sink #v[decider], .sink #v[inputL]] :
      AtomicProcs Op χ V) =
      [.async (.forward 1) [inputR] [output], .async (.sink 1) [decider] [],
        .async (.sink 1) [inputL] []] := by
    simp [AtomicProc.forward, AtomicProc.sink]
  have hnd := (haff.atom_nodup h₁).1
  simp at hnd
  obtain ⟨⟨hdl, hdr⟩, hlr⟩ := hnd
  -- The carry alternates between `popRight` and `decider` (always true);
  -- `inputL` is never read. Same channels on both sides.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    (L₀ = [.async (.merge .popRight 1) [decider, inputL, inputR] [output]] ∨
      L₀ = [.async (.merge .decider 1) [decider, inputL, inputR] [output]]) ∧
    L₁ = [.async (.forward 1) [inputR] [output], .async (.sink 1) [decider] [],
      .async (.sink 1) [inputL] []] ∧
    chans₀ = chans₁, ?_, ?_⟩
  · constructor
    · simp
    · simp [(List.getElem?_eq_some_iff.mp h₁).1]
    · simp [hP', Ne.symm hdr, Ne.symm hlr, hdl]
    · simp [hP']
    · simp [hP', hP]
    · simp [hP', hP]
  · constructor
    · exact ⟨.inl hP, hP', rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ x w chans₀' _ _ ⟨hL₀, rfl, rfl⟩ hpop
      exact ⟨_, hpop, hL₀, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ _ _ _ ⟨hL₀, rfl, rfl⟩
      exact ⟨hL₀, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨hL₀, rfl, rfl⟩ hmem
      rcases hL₀ with rfl | rfl <;> simp at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' hinv _ ⟨hL₀, rfl, rfl⟩ hget hinterp
        hlen₁ _ hpop
      obtain ⟨st, hst, rfl⟩ : ∃ st, (st = .popRight ∨ st = .decider) ∧
          L₀ = [.async (.merge st 1) [decider, inputL, inputR] [output]] := by
        rcases hL₀ with rfl | rfl
        · exact ⟨_, .inl rfl, rfl⟩
        · exact ⟨_, .inr rfl, rfl⟩
      match i, hget with
      | 0, hget =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        rcases hinterp.merge_inv hlen₁ with
          ⟨rfl, -⟩ | ⟨rfl, rfl, rfl, rfl, w, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, dv, b, rfl, hb, rfl⟩
        · -- `popLeft` is unreachable.
          simp at hst
        · -- `popRight`: the forward fires.
          refine ⟨_, _, LocalTauStar.async_list_mem
            (aop := .forward 1) (allInputs := [inputR]) (allOutputs := [output])
            (inputs := [inputR]) (outputs := [output])
            (by simp) (.interp_forward rfl rfl) rfl rfl hpop, .inr (by simp), rfl, rfl⟩
        · -- `decider`: the decider is always true, so the sink of `decider` fires.
          have hpd := hpop decider
          simp at hpd
          have hdv : dv = v := hconst.eq_of_mem hinv dv (by simp [hpd])
          rw [hdv, hbool] at hb
          obtain rfl : b = true := (Option.some.inj hb).symm
          refine ⟨_, _, LocalTauStar.async_list_mem
            (aop := .sink 1) (allInputs := [decider]) (allOutputs := [])
            (inputs := [decider]) (outputs := []) (outputVals := [])
            (by simp) (.interp_sink rfl) rfl rfl hpop, .inl (by simp), rfl, rfl⟩
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨hP'.symm, rfl⟩

end Wavelet.Compile.DeadCodeElim
