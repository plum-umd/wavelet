import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! `carry-steer-cycle-to-sink`/`carry-order-steer-cycle-to-sink`:
a carry-steer cycle with the same decider is a sink (only a forward simulation
without `PreservesInit`, since the sink may leave unconsumed values). -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

/-- A pattern of async atoms whose outputs are all read by the pattern itself
has no visible effect other than consuming its inputs. So it can be replaced
by any atoms that never fire: the rewritten channels lag behind (`lag`) on the
inputs of the pattern, and the outputs of the pattern are unconstrained. -/
private theorem closed_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {I : List Nat} {P' : AtomicProcs Op χ V}
  (hnames : RewriteNames proc I P')
  (hasync : ∀ ap ∈ matchedOf proc.atoms I, ∀ (o : Op) ins outs, ap ≠ .op o ins outs)
  (hclosed : ∀ x ∈ AtomicProcs.outputNames (matchedOf proc.atoms I),
    x ∈ AtomicProcs.inputNames (matchedOf proc.atoms I)) :
    RuleOKNoInit proc I P' := by
  refine ⟨hnames, λ _ chans₀ L₁ chans₁ =>
    L₁ = P' ∧ ∃ lag : χ → List V,
      (∀ y, y ∉ AtomicProcs.outputNames (matchedOf proc.atoms I) →
        chans₁ y = lag y ++ chans₀ y) ∧
      (∀ y, y ∉ AtomicProcs.inputNames (matchedOf proc.atoms I) → lag y = []), ?_⟩
  constructor
  · exact ⟨rfl, λ _ => [], λ _ _ => rfl, λ _ _ => rfl⟩
  · rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, lag, heq, hlag⟩ hpop
    have hx' : x ∉ AtomicProcs.outputNames (matchedOf proc.atoms I) :=
      λ h => hx (hclosed x h)
    refine ⟨λ y => if y ∈ AtomicProcs.outputNames (matchedOf proc.atoms I) then chans₁ y
      else lag y ++ chans₀' y, ?_, rfl, lag, ?_, hlag⟩
    · intro y
      by_cases hy : y ∈ AtomicProcs.outputNames (matchedOf proc.atoms I)
      · have : y ≠ x := by rintro rfl; exact hx' hy
        simp [hy, this]
      · rw [heq y hy, hpop y]
        by_cases hyx : y = x
        · subst hyx; simp [hy, hlag y hx]
        · simp [hy, hyx]
    · intro y hy
      simp [hy]
  · rintro L₀ chans₀ L₁ chans₁ outs vals _ _ _ _ ⟨rfl, lag, heq, hlag⟩
    exact ⟨rfl, lag, λ y hy => by simp [heq y hy], hlag⟩
  · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
      _ hshape _ hmem
    exact absurd rfl (hasync _ (forall₂_sameShape_op_mem hshape hmem) op inputs outputs)
  · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
      inputs outputs inputVals outputVals chans₀' _ hshape ⟨rfl, lag, heq, hlag⟩ hget hinterp
      _ _ hpop
    -- The fired atom is one of the matched atoms
    obtain ⟨ap₀, hget₀, hshape₀⟩ := forall₂_sameShape_getElem? hshape hget
    have hmem₀ := List.mem_of_getElem? hget₀
    have hins := hshape₀.inputs_eq
    have houts := hshape₀.outputs_eq
    simp only [AtomicProc.inputs_async, AtomicProc.outputs_async] at hins houts
    have hin : ∀ x ∈ inputs, x ∈ AtomicProcs.inputNames (matchedOf proc.atoms I) := by
      intro x hx
      simp only [AtomicProcs.inputNames, List.mem_flatMap]
      exact ⟨ap₀, hmem₀, hins ▸ hinterp.input_sublist.subset hx⟩
    have hout : ∀ x ∈ outputs, x ∈ AtomicProcs.outputNames (matchedOf proc.atoms I) := by
      intro x hx
      simp only [AtomicProcs.outputNames, List.mem_flatMap]
      exact ⟨ap₀, hmem₀, houts ▸ hinterp.output_sublist.subset hx⟩
    -- Nothing fires in the rewritten graph
    refine ⟨_, _, .refl, rfl, λ y => lag y ++ ChanMap.pushed inputs inputVals y, ?_, ?_⟩
    · intro y hy
      have : y ∉ outputs := λ h => hy (hout y h)
      dsimp only
      rw [heq y hy, hpop y, ChanMap.pushed_not_mem this]
      simp
    · intro y hy
      have : y ∉ inputs := λ h => hy (hin y h)
      dsimp only
      rw [hlag y hy, ChanMap.pushed_not_mem this]
      rfl

private theorem sink_inputs [Arity Op] {xs : Vector χ k} :
    (AtomicProc.sink (Op := Op) (V := V) xs).inputs = xs.toList := by
  unfold AtomicProc.sink
  split
  · rfl
  · rename_i h
    obtain rfl : k = 0 := by simpa using h
    simp

private theorem sink_outputs [Arity Op] {xs : Vector χ k} :
    (AtomicProc.sink (Op := Op) (V := V) xs).outputs = [] := by
  unfold AtomicProc.sink
  split <;> rfl

theorem carry_steer_cycle_to_sink_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {decider inputL inputR output decider' : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .popLeft 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.steer true 1) [decider', output] [inputR]))
  (hne : i₂ ≠ i₁) :
    RuleOKNoInit proc [i₂, i₁] [.sink #v[decider, decider', inputL]]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.steer true 1) [decider', output] [inputR],
        .async (.merge .popLeft 1) [decider, inputL, inputR] [output]] := by
    simp [h₁, h₂]
  have hP' : ([.sink #v[decider, decider', inputL]] : AtomicProcs Op χ V) =
      [.async (.sink 3) [decider, decider', inputL] []] := by
    simp [AtomicProc.sink]
  -- Facts from affineness
  have hnd₁ := (haff.atom_nodup h₁).1
  have hdisj := (haff.atom_disjoint h₂ h₁ hne).1
  simp at hnd₁ hdisj
  obtain ⟨⟨hdl, -⟩, -⟩ := hnd₁
  obtain ⟨⟨hdd', -⟩, ⟨hld', -⟩, -⟩ := hdisj
  -- The cycle only feeds itself, so the sink never needs to fire
  apply closed_ok
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp [hP', hdd', hdl, Ne.symm hld']
    · simp [hP']
    · simp [hP', hP]
    · simp [hP']
  · simp [hP]
  · simp [hP]

theorem carry_order_steer_cycle_to_sink_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ i₃ : Nat}
  {k : Nat} [NeZero k] {decider inputL inputR output decider' output' : χ} {inputs'' : List χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .popLeft 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.steer true 1) [decider', output] [output']))
  (h₃ : proc.atoms[i₃]? = some (.async (.order k) inputs'' [inputR]))
  (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
  (hmem : output' ∈ inputs'') :
    RuleOKNoInit proc [i₃, i₂, i₁] [
      .sink (#v[decider, decider', inputL] ++ (inputs''.erase output').toVector),
    ]
  := by
  have hP : matchedOf proc.atoms [i₃, i₂, i₁] =
      [.async (.order k) inputs'' [inputR],
        .async (.steer true 1) [decider', output] [output'],
        .async (.merge .popLeft 1) [decider, inputL, inputR] [output]] := by
    simp [h₁, h₂, h₃]
  have hins : (AtomicProc.sink (Op := Op) (V := V)
      (#v[decider, decider', inputL] ++ (inputs''.erase output').toVector)).inputs =
      [decider, decider', inputL] ++ inputs''.erase output' := by
    simp [sink_inputs, List.toVector]
  -- Facts from affineness
  have hnd₁ := (haff.atom_nodup h₁).1
  have hnd₃ := (haff.atom_nodup h₃).1
  have hdisj₂₁ := (haff.atom_disjoint h₂ h₁ hne₂₁).1
  have hdisj₃₁ := (haff.atom_disjoint h₃ h₁ hne₃₁).1
  have hdisj₃₂ := (haff.atom_disjoint h₃ h₂ hne₃₂).1
  simp at hnd₁ hnd₃ hdisj₂₁ hdisj₃₁ hdisj₃₂
  obtain ⟨⟨hdl, -⟩, -⟩ := hnd₁
  obtain ⟨⟨hdd', -⟩, ⟨hld', -⟩, -⟩ := hdisj₂₁
  obtain ⟨hd₃, hl₃, -⟩ := hdisj₃₁
  obtain ⟨hd'₃, -⟩ := hdisj₃₂
  -- The cycle only feeds itself, so the sink never needs to fire
  apply closed_ok
  · constructor
    · simp [hne₃₂, hne₃₁, hne₂₁]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1,
        (List.getElem?_eq_some_iff.mp h₃).1]
    · simp only [AtomicProcs.inputNames_cons, AtomicProcs.inputNames_nil, List.append_nil, hins]
      refine List.nodup_append.mpr ⟨by simp [hdd', hdl, Ne.symm hld'], hnd₃.erase _, ?_⟩
      intro x hx y hy
      have hy := List.mem_of_mem_erase hy
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact λ h => hd₃ (h ▸ hy)
      · exact λ h => hd'₃ (h ▸ hy)
      · exact λ h => hl₃ (h ▸ hy)
    · simp [sink_outputs]
    · intro x hx
      simp only [AtomicProcs.inputNames_cons, AtomicProcs.inputNames_nil, List.append_nil,
        hins] at hx
      left
      simp only [hP, AtomicProcs.inputNames_cons, AtomicProcs.inputNames_nil,
        AtomicProc.inputs_async, List.append_nil, List.mem_append]
      simp at hx
      rcases hx with rfl | rfl | rfl | hx
      · simp
      · simp
      · simp
      · exact .inl (List.mem_of_mem_erase hx)
    · simp [sink_outputs]
  · simp [hP]
  · simp [hP, hmem]

end Wavelet.Compile.DeadCodeElim
