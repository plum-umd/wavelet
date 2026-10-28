import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Extract.Basic

/-! Symbolic execution of the `steer` branch of `deadCodeElim`. -/

namespace Wavelet.Compile.DeadCodeElim.Extract

open Semantics Dataflow

variable {Op χ V : Type} [Arity Op] [DecidableEq χ] [Hashable χ] [InterpConsts V]

theorem branch_steer_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {flavor : Bool} {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.steer flavor 1) inputs outputs))
  (h : (
    .assume (inputs.length = 2 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let input := inputs[1]'(by omega)
    let output := outputs[0]'(by omega)
    (do
      let val ← .checkFromConst decider
      if let some val := InterpConsts.toBool val then
        if val = flavor then
          .apply "steer-const-true" [.order #v[input, decider] output]
        else
          .apply "steer-const-false" [
            .sink #v[input],
            .sink #v[decider],
            .inact #v[output],
          ]
      else failure) <|>
    .chooseWithNames (inputs ++ outputs) λ
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if output = sink then
        .apply "steer-sink" [
          .sink #v[input],
          .sink #v[decider],
        ]
      else failure
    | .async (.steer flavor' 1) inputs' outputs' =>
      .assume (inputs'.length = 2 ∧ outputs'.length = 1) λ h => do
      let decider' := inputs'[0]'(by omega)
      let input' := inputs'[1]'(by omega)
      let output' := outputs'[0]'(by omega)
      .assumeFromSameFork decider decider'
      if flavor = flavor' ∧ output = input' then
        .apply "steer-steer" [
          .steer flavor decider #v[input] #v[output'],
          .sink #v[decider'],
        ]
      else
        failure
    | .async (AsyncOp.order n) inputs' outputs' =>
      .assume (n > 0 ∧ inputs'.length = n ∧ outputs'.length = 1) λ h => do
      let output' := outputs'[0]'(by omega)
      let inputs' ← inputs'.toVectorDyn n
      if output ∈ inputs' then
        .chooseWithNames [output'] λ
        | .async (.steer flavor'' 1) inputs'' outputs'' => do
          .assume (inputs''.length = 2 ∧ outputs''.length = 1) λ h => do
          let decider'' := inputs''[0]'(by omega)
          let input'' := inputs''[1]'(by omega)
          let output'' := outputs''[0]'(by omega)
          if flavor = flavor'' ∧ output' = input'' then
            .assumeFromSameFork decider decider''
            .apply "steer-order-steer" [
              .steer flavor decider #v[input] #v[output],
              .order inputs' output'',
              .sink #v[decider''],
            ]
          else failure
        | _ => failure
      else failure
    | .async (.fork n) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = n) λ h => do
      let input' := inputs'[0]'(by omega)
      let outputs' ← outputs'.toVectorDyn n
      .chooseWithNames outputs'.toList λ
      | .async (.steer flavor'' 1) inputs'' outputs'' =>
        .assume (inputs''.length = 2 ∧ outputs''.length = 1) λ h => do
        let decider'' := inputs''[0]'(by omega)
        let input'' := inputs''[1]'(by omega)
        let output'' := outputs''[0]'(by omega)
        if flavor = flavor'' then
          .assumeFromSameFork decider decider''
          (do
            .assumeFromSameFork input input''
            .apply "par-steer-steer" [
              .fork input' outputs',
              .steer flavor decider #v[input] #v[.rename 0 output],
              .sink #v[decider''],
              .sink #v[input''],
              .fork (.rename 0 output) #v[output, output''],
            ]) <|>
          (do
            if input'' ∈ outputs' ∧ input' ∈ outputs then
              .apply "steer-fork-steer" [
                .fork input' (outputs'.push output''),
                .sink #v[decider''],
                .sink #v[input''],
                .steer flavor decider #v[input] #v[output],
              ]
            else failure)
        else failure
      | _ => failure
    | .async (.const v 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 1) λ h => do
      let act := inputs'[0]'(by omega)
      let output' := outputs'[0]'(by omega)
      if output' = input then
        .apply "const-steer" [
          .steer flavor decider #v[act] #v[.rename 0 act],
          .const v (.rename 0 act) #v[output],
        ]
      else failure
    | _ => failure : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨decider, input, rfl⟩ := length_eq_two hlen₁
  obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hlen₂
  dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
  replace h := StateT.orElse_some h
  rcases h with h | h
  · -- `steer-const-*`
    replace ⟨v, s₁, h₁, h⟩ := StateT.bind_some h
    obtain ⟨rfl, hconst⟩ := RewriteM.checkFromConst_some' h₁
    generalize hb : InterpConsts.toBool v = b at h
    split at h
    · rename_i b
      split at h
      · rename_i heq
        subst heq
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        exact ⟨rfl, .steer_const_true hap hconst hb⟩
      · rename_i hne
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        exact ⟨rfl, .steer_const_false hap hconst hb hne⟩
    · exact (StateT.failure_some h).elim
  replace ⟨i₂, ap₂, hi₂, hap₂, h⟩ := RewriteM.chooseWithNames_some' h
  have hne₂₁ := ne_of_not_mem_singleton hi₂
  split at h
  · -- `steer-sink`
    replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨sink, rfl⟩ := List.length_eq_one_iff.mp hlen₃
    obtain rfl := List.eq_nil_of_length_eq_zero hlen₄
    dsimp only [List.getElem_cons_zero] at h
    split at h
    · rename_i heq
      subst heq
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .steer_sink hap hap₂ hne₂₁⟩
    · exact (StateT.failure_some h).elim
  · -- `steer-steer` (excluded)
    replace ⟨_, h⟩ := RewriteM.assume_some h
    dsimp only at h
    replace ⟨_, s₂, h₁, h⟩ := StateT.bind_some h
    obtain ⟨rfl, -⟩ := RewriteM.assumeFromSameFork_some' h₁
    split at h
    · obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .excluded (by simp [excludedRules])⟩
    · exact (StateT.failure_some h).elim
  · -- `steer-order-steer` (excluded)
    replace ⟨_, h⟩ := RewriteM.assume_some h
    dsimp only at h
    replace ⟨_, s₂, h₁, h⟩ := StateT.bind_some h
    obtain ⟨_, rfl, rfl⟩ := List.toVectorDyn_some h₁
    split at h
    · replace ⟨i₃, ap₃, _, _, h⟩ := RewriteM.chooseWithNames_some' h
      split at h
      · replace ⟨_, h⟩ := RewriteM.assume_some h
        dsimp only at h
        split at h
        · replace ⟨_, s₃, h₁, h⟩ := StateT.bind_some h
          obtain ⟨rfl, -⟩ := RewriteM.assumeFromSameFork_some' h₁
          obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
          exact ⟨rfl, .excluded (by simp [excludedRules])⟩
        · exact (StateT.failure_some h).elim
      · exact (StateT.failure_some h).elim
    · exact (StateT.failure_some h).elim
  · -- `par-steer-steer` and `steer-fork-steer` (excluded)
    rename_i n inputs' outputs'
    replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨input', rfl⟩ := List.length_eq_one_iff.mp hlen₃
    dsimp only [List.getElem_cons_zero] at h
    replace ⟨_, s₂, h₁, h⟩ := StateT.bind_some h
    obtain ⟨hlen₄', rfl, rfl⟩ := List.toVectorDyn_some h₁
    replace ⟨i₃, ap₃, hi₃, hap₃, h⟩ := RewriteM.chooseWithNames_some' h
    have ⟨hne₃₂, hne₃₁⟩ := ne_of_not_mem_pair hi₃
    split at h
    · replace ⟨⟨hlen₅, hlen₆⟩, h⟩ := RewriteM.assume_some h
      obtain ⟨decider'', input'', rfl⟩ := length_eq_two hlen₅
      obtain ⟨output'', rfl⟩ := List.length_eq_one_iff.mp hlen₆
      dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      split at h
      · rename_i heq
        subst heq
        replace ⟨_, s₃, h₁, h⟩ := StateT.bind_some h
        obtain ⟨rfl, hfork₁⟩ := RewriteM.assumeFromSameFork_some' h₁
        replace h := StateT.orElse_some h
        rcases h with h | h
        · replace ⟨_, s₄, h₁, h⟩ := StateT.bind_some h
          obtain ⟨rfl, hfork₂⟩ := RewriteM.assumeFromSameFork_some' h₁
          obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
          have hfork : AtomicProc.fork input' (outputs'.toVector.cast hlen₄') =
              (.async (.fork n) [input'] outputs' : AtomicProc Op (RewriteName χ) V) := by
            simp [AtomicProc.fork, List.toVector]
          refine ⟨rfl, ?_⟩
          rw [hfork]
          exact .par_steer_steer hap hap₂ hap₃ hne₂₁ hne₃₁ hne₃₂ hlen₄ hfork₁ hfork₂
        · split at h
          · obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
            exact ⟨rfl, .excluded (by simp [excludedRules])⟩
          · exact (StateT.failure_some h).elim
      · exact (StateT.failure_some h).elim
    · exact (StateT.failure_some h).elim
  · -- `const-steer`
    replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨act, rfl⟩ := List.length_eq_one_iff.mp hlen₃
    obtain ⟨output', rfl⟩ := List.length_eq_one_iff.mp hlen₄
    dsimp only [List.getElem_cons_zero] at h
    split at h
    · rename_i heq
      subst heq
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .const_steer hap hap₂ hne₂₁⟩
    · exact (StateT.failure_some h).elim
  · exact (StateT.failure_some h).elim

end Wavelet.Compile.DeadCodeElim.Extract
