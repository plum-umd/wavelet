import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Extract.Basic

/-! Symbolic execution of the n-ary `order` branch of `deadCodeElim`. -/

namespace Wavelet.Compile.DeadCodeElim.Extract

open Semantics Dataflow

variable {Op χ V : Type} [Arity Op] [DecidableEq χ] [Hashable χ] [InterpConsts V]

theorem branch_order_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {n : Nat} [NeZero n] {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.order n) inputs outputs))
  (h : (
    .assume (n > 1 ∧ inputs.length = n ∧ outputs.length = 1) λ h => do
    let output := outputs[0]'(by omega)
    .chooseWithNames (inputs ++ outputs) λ
    | .async (AsyncOp.order m) inputs' outputs' =>
      .assume (m > 1 ∧ inputs'.length = m ∧ outputs'.length = 1) λ h => do
      let output' := outputs'[0]'(by omega)
      if output ∈ inputs' then
        let newInputs' := inputs'
          |>.map (λ name => if name = output then inputs else [name])
          |>.flatten
        .assume (newInputs'.length ≠ 0) λ h' => do
        let : NeZero newInputs'.length := by constructor; omega
        .apply "order-order" [
          .order newInputs'.toVector output',
        ]
      else
        failure
    | .async (.fork m) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = m) λ h =>
      let input' := inputs'[0]'(by omega)
      (inputs.drop 1).firstM λ input₁ =>
        if input₁ ∈ outputs' then
          inputs.firstM λ input₂ => do
            if input₁ ≠ input₂ then
              .checkSyncPathTo input₂ outputs' ((← get).aps.length + 1)
              let newInputs := inputs.erase input₁
              let newOutputs' := outputs'.erase input₁
              .assume (newInputs.length ≠ 0) λ h' => do
              let : NeZero newInputs.length := by constructor; omega
              .apply "order-sync-path" [
                .fork input' newOutputs'.toVector,
                .order newInputs.toVector output,
              ]
            else failure
        else failure
    | .async (AsyncOp.sink n) inputs' outputs' =>
      .assume (n > 0 ∧ inputs'.length = n ∧ outputs'.length = 0) λ _ => do
      if output ∈ inputs' then
        .apply "order-sink" [
          .sink inputs.toVector,
          .sink (inputs'.erase output).toVector,
        ]
      else failure
    | .async (.const v 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 1) λ h => do
      let act := inputs'[0]'(by omega)
      let output' := outputs'[0]'(by omega)
      if output' ∈ inputs ∧ output' ≠ inputs[0] then
        let : NeZero (inputs.erase output' ++ [act]).length := by constructor; simp
        .apply "order-const" [
          .order (inputs.erase output' ++ [act]).toVector output,
        ]
      else if output' = inputs[0] then
        let : NeZero (act :: inputs.tail).length := by constructor; simp
        .apply "order-const-head" [
          .order (act :: inputs.tail).toVector output',
          .const v output' #v[output],
        ]
      else failure
    | .async (AsyncOp.steer flavor 1) inputs₁ outputs₁ =>
      .assume (n = 2) λ h₁ => do
      let orderInput₁ := inputs[0]'(by omega)
      let orderInput₂ := inputs[1]'(by omega)
      .assume (inputs₁.length = 2 ∧ outputs₁.length = 1) λ h₂ => do
      let decider₁ := inputs₁[0]'(by omega)
      let input₁ := inputs₁[1]'(by omega)
      let output₁ := outputs₁[0]'(by omega)
      .chooseWithNames (inputs ++ outputs) λ
      | .async (AsyncOp.steer flavor' 1) inputs₂ outputs₂ =>
        .assume (inputs₂.length = 2 ∧ outputs₂.length = 1) λ h₃ => do
        let decider₂ := inputs₂[0]'(by omega)
        let input₂ := inputs₂[1]'(by omega)
        let output₂ := outputs₂[0]'(by omega)
        .assumeFromSameFork decider₁ decider₂
        if flavor = flavor' ∧ output₁ = orderInput₁ ∧ output₂ = orderInput₂ then
          .apply "order-steer-steer" [
            .order #v[input₁, input₂] output₁,
            .steer flavor decider₁ #v[output₁] #v[output],
            .sink #v[decider₂],
          ]
        else failure
      | _ => failure
    | _ => failure : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hn, hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hlen₂
  dsimp only [List.getElem_cons_zero] at h
  replace ⟨i₂, ap₂, hi₂, hap₂, h⟩ := RewriteM.chooseWithNames_some' h
  have hne₂₁ := ne_of_not_mem_singleton hi₂
  split at h
  · -- `order-order`
    replace ⟨⟨hk, hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨output', rfl⟩ := List.length_eq_one_iff.mp hlen₄
    dsimp only [List.getElem_cons_zero] at h
    split at h
    · rename_i hmem
      replace ⟨hne, h⟩ := RewriteM.assume_some h
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      haveI := NeZero.mk hne
      exact ⟨rfl, .order_order hap hap₂ hne₂₁ hn hlen₁ hk hlen₃ hmem rfl⟩
    · exact (StateT.failure_some h).elim
  · -- `order-sync-path`
    replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨input', rfl⟩ := List.length_eq_one_iff.mp hlen₃
    dsimp only [List.getElem_cons_zero] at h
    replace ⟨input₁, hmem₁, h⟩ := List.firstM_some h
    split at h
    · rename_i hmem₂
      replace ⟨input₂, _, h⟩ := List.firstM_some h
      split at h
      · replace h := StateT.get_bind_some h
        replace ⟨_, s₃, h₁, h⟩ := StateT.bind_some h
        obtain rfl := RewriteM.checkSyncPathTo_some' h₁
        replace ⟨hne, h⟩ := RewriteM.assume_some h
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        haveI := NeZero.mk hne
        exact ⟨rfl, .order_sync_path hap hap₂ hne₂₁ hn hlen₁ hlen₄ hmem₁ hmem₂⟩
      · exact (StateT.failure_some h).elim
    · exact (StateT.failure_some h).elim
  · -- `order-sink`
    replace ⟨⟨hk, hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain rfl := List.eq_nil_of_length_eq_zero hlen₄
    split at h
    · rename_i hmem
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .order_sink hap hap₂ hne₂₁ hn hlen₁ hlen₃ hmem⟩
    · exact (StateT.failure_some h).elim
  · -- `order-const` and `order-const-head`
    replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨act, rfl⟩ := List.length_eq_one_iff.mp hlen₃
    obtain ⟨output', rfl⟩ := List.length_eq_one_iff.mp hlen₄
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < inputs.length)
    dsimp only [List.getElem_cons_zero, List.tail_cons] at h
    split at h
    · rename_i hcond
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      have hmem : output' ∈ rest := by
        rcases List.mem_cons.mp hcond.1 with h' | h'
        · exact absurd h' hcond.2
        · exact h'
      haveI : NeZero ((first :: rest).erase output' ++ [act]).length := ⟨by simp⟩
      exact ⟨rfl, .order_const (first := first) (rest := rest) (act := act) (output' := output')
        hap hap₂ hne₂₁ hn hlen₁ hmem hcond.2⟩
    · split at h
      · rename_i heq
        subst heq
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        haveI : NeZero (act :: rest).length := ⟨by simp⟩
        exact ⟨rfl, .order_const_head (act := act) (rest := rest) hap hap₂ hne₂₁ hn hlen₁⟩
      · exact (StateT.failure_some h).elim
  · -- `order-steer-steer`
    replace ⟨hn₂, h⟩ := RewriteM.assume_some h
    subst hn₂
    obtain ⟨orderInput₁, orderInput₂, rfl⟩ := length_eq_two hlen₁
    replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨decider₁, input₁, rfl⟩ := length_eq_two hlen₃
    obtain ⟨output₁, rfl⟩ := List.length_eq_one_iff.mp hlen₄
    dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
    replace ⟨i₃, ap₃, hi₃, hap₃, h⟩ := RewriteM.chooseWithNames_some' h
    have ⟨hne₃₂, hne₃₁⟩ := ne_of_not_mem_pair hi₃
    split at h
    · replace ⟨⟨hlen₅, hlen₆⟩, h⟩ := RewriteM.assume_some h
      obtain ⟨decider₂, input₂, rfl⟩ := length_eq_two hlen₅
      obtain ⟨output₂, rfl⟩ := List.length_eq_one_iff.mp hlen₆
      dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      replace ⟨_, s₃, h₁, h⟩ := StateT.bind_some h
      obtain ⟨rfl, hfork⟩ := RewriteM.assumeFromSameFork_some' h₁
      split at h
      · rename_i hcond
        obtain ⟨rfl, rfl, rfl⟩ := hcond
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        exact ⟨rfl, .order_steer_steer hap hap₂ hap₃ hne₂₁ hne₃₁ hne₃₂ hfork⟩
      · exact (StateT.failure_some h).elim
    · exact (StateT.failure_some h).elim
  · exact (StateT.failure_some h).elim

end Wavelet.Compile.DeadCodeElim.Extract
