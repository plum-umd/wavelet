import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Extract.Basic

/-! Symbolic execution of the `merge` (and carry) branches of `deadCodeElim`. -/

namespace Wavelet.Compile.DeadCodeElim.Extract

open Semantics Dataflow

variable {Op χ V : Type} [Arity Op] [DecidableEq χ] [Hashable χ] [InterpConsts V]

theorem branch_carry_left_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.merge .popLeft 1) inputs outputs))
  (h : (
    .assume (inputs.length = 3 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let inputL := inputs[1]'(by omega)
    let inputR := inputs[2]'(by omega)
    let output := outputs[0]'(by omega)
    (do
      .chooseWithNames outputs λ
      | .async (.fork 2) inputs' outputs' =>
        .assume (inputs'.length = 1 ∧ outputs'.length = 2) λ h =>
        let input' := inputs'[0]'(by omega)
        let output₁' := outputs'[0]'(by omega)
        let output₂' := outputs'[1]'(by omega)
        if output = input' then
          .chooseWithNames outputs' λ
          | .async (.steer true 1) inputs'' outputs'' =>
            .assume (inputs''.length = 2 ∧ outputs''.length = 1) λ h => do
            let decider'' := inputs''[0]'(by omega)
            let input'' := inputs''[1]'(by omega)
            let output'' := outputs''[0]'(by omega)
            .assumeFromSameFork decider decider''
            if output'' = inputR then
              if input'' = output₁' then
                .apply "carry-fork-steer-to-inv-left" [
                  .inv true none decider inputL output₂',
                  .sink #v[decider''],
                ]
              else if input'' = output₂' then
                .apply "carry-fork-steer-to-inv-right" [
                  .inv true none decider inputL output₁',
                  .sink #v[decider''],
                ]
              else failure
            else failure
          | _ => failure
        else failure
      | .async (.steer true 1) inputs' outputs' =>
        .assume (inputs'.length = 2 ∧ outputs'.length = 1) λ h => do
        let decider' := inputs'[0]'(by omega)
        let input' := inputs'[1]'(by omega)
        let output' := outputs'[0]'(by omega)
        .assumeFromSameFork decider decider'
        if output = input' ∧ output' = inputR then
          .apply "carry-steer-cycle-to-sink" [.sink #v[decider, decider', inputL]]
        else
          .chooseWithNames [output'] λ
          | .async (AsyncOp.order n) inputs'' outputs'' =>
            .assume (n > 0 ∧ inputs''.length = n ∧ outputs''.length = 1) λ h => do
            let output'' := outputs''[0]'(by omega)
            if output = input' ∧ output' ∈ inputs'' ∧ output'' = inputR then
              .apply "carry-order-steer-cycle-to-sink" [
                .sink (#v[
                  decider, decider', inputL,
                ] ++ (inputs''.erase output').toVector)
              ]
            else failure
          | _ => failure
      | _ => failure) <|>
    (do
      let val ← .checkFromConst decider
      if let some val := InterpConsts.toBool val then
        if ¬val then
          return ← .apply "carry-false" [
            .forward #v[inputL] #v[output],
            .sink #v[decider],
            .sink #v[inputR],
          ]
      failure) : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨decider, inputL, inputR, rfl⟩ := length_eq_three hlen₁
  obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hlen₂
  dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
  replace h := StateT.orElse_some h
  rcases h with h | h
  · replace ⟨i₂, ap₂, hi₂, hap₂, h⟩ := RewriteM.chooseWithNames_some' h
    have hne₂₁ := ne_of_not_mem_singleton hi₂
    split at h
    · -- `carry-fork-steer-to-inv-*`
      replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
      obtain ⟨input', rfl⟩ := List.length_eq_one_iff.mp hlen₃
      obtain ⟨output₁', output₂', rfl⟩ := length_eq_two hlen₄
      dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      split at h
      · rename_i heq
        subst heq
        replace ⟨i₃, ap₃, hi₃, hap₃, h⟩ := RewriteM.chooseWithNames_some' h
        have ⟨hne₃₂, hne₃₁⟩ := ne_of_not_mem_pair hi₃
        split at h
        · replace ⟨⟨hlen₅, hlen₆⟩, h⟩ := RewriteM.assume_some h
          obtain ⟨decider'', input'', rfl⟩ := length_eq_two hlen₅
          obtain ⟨output'', rfl⟩ := List.length_eq_one_iff.mp hlen₆
          dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
          replace ⟨_, s₃, h₁, h⟩ := StateT.bind_some h
          obtain ⟨rfl, hfork⟩ := RewriteM.assumeFromSameFork_some' h₁
          split at h
          · rename_i heq
            subst heq
            split at h
            · rename_i heq
              subst heq
              obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
              exact ⟨rfl, .carry_fork_steer_to_inv_left hap hap₂ hap₃ hne₂₁ hne₃₁ hne₃₂ hfork⟩
            · split at h
              · rename_i hne heq
                subst heq
                obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
                exact ⟨rfl, .carry_fork_steer_to_inv_right hap hap₂ hap₃ hne₂₁ hne₃₁ hne₃₂ hne
                  hfork⟩
              · exact (StateT.failure_some h).elim
          · exact (StateT.failure_some h).elim
        · exact (StateT.failure_some h).elim
      · exact (StateT.failure_some h).elim
    · -- `carry-steer-cycle-to-sink` and `carry-order-steer-cycle-to-sink`
      replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
      obtain ⟨decider', input', rfl⟩ := length_eq_two hlen₃
      obtain ⟨output', rfl⟩ := List.length_eq_one_iff.mp hlen₄
      dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      replace ⟨_, s₃, h₁, h⟩ := StateT.bind_some h
      obtain ⟨rfl, hfork⟩ := RewriteM.assumeFromSameFork_some' h₁
      split at h
      · rename_i hcond
        obtain ⟨rfl, rfl⟩ := hcond
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        exact ⟨rfl, .carry_steer_cycle_to_sink hap hap₂ hne₂₁ hfork⟩
      · replace ⟨i₃, ap₃, hi₃, hap₃, h⟩ := RewriteM.chooseWithNames_some' h
        have ⟨hne₃₂, hne₃₁⟩ := ne_of_not_mem_pair hi₃
        split at h
        · replace ⟨⟨hk, hlen₅, hlen₆⟩, h⟩ := RewriteM.assume_some h
          obtain ⟨output'', rfl⟩ := List.length_eq_one_iff.mp hlen₆
          dsimp only [List.getElem_cons_zero] at h
          split at h
          · rename_i hcond
            obtain ⟨rfl, hmem, rfl⟩ := hcond
            obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
            exact ⟨rfl, .carry_order_steer_cycle_to_sink hap hap₂ hap₃ hne₂₁ hne₃₁ hne₃₂ hlen₅ hmem
              hfork⟩
          · exact (StateT.failure_some h).elim
        · exact (StateT.failure_some h).elim
    · exact (StateT.failure_some h).elim
  · -- `carry-false`
    replace ⟨v, s₁, h₁, h⟩ := StateT.bind_some h
    obtain ⟨rfl, hconst⟩ := RewriteM.checkFromConst_some' h₁
    generalize hb : InterpConsts.toBool v = b at h
    split at h
    · rename_i b
      split at h
      · rename_i hbf
        obtain rfl : b = false := by simpa using hbf
        replace h := StateT.bind_pure_some h
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        exact ⟨rfl, .carry_false hap hconst hb⟩
      · replace ⟨_, _, _, h⟩ := StateT.bind_some h
        exact (StateT.failure_some h).elim
    · replace ⟨_, _, _, h⟩ := StateT.bind_some h
      exact (StateT.failure_some h).elim

theorem branch_carry_right_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.merge .popRight 1) inputs outputs))
  (h : (
    .assume (inputs.length = 3 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let inputL := inputs[1]'(by omega)
    let inputR := inputs[2]'(by omega)
    let output := outputs[0]'(by omega)
    let val ← .checkFromConst decider
    if let some val := InterpConsts.toBool val then
      if val then
        return ← .apply "carry-true" [
          .forward #v[inputR] #v[output],
          .sink #v[decider],
          .sink #v[inputL],
        ]
    failure : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨decider, inputL, inputR, rfl⟩ := length_eq_three hlen₁
  obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hlen₂
  dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
  replace ⟨v, s₁, h₁, h⟩ := StateT.bind_some h
  obtain ⟨rfl, hconst⟩ := RewriteM.checkFromConst_some' h₁
  generalize hb : InterpConsts.toBool v = b at h
  split at h
  · rename_i b
    split at h
    · rename_i hbt
      subst hbt
      replace h := StateT.bind_pure_some h
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .carry_true hap hconst hb⟩
    · replace ⟨_, _, _, h⟩ := StateT.bind_some h
      exact (StateT.failure_some h).elim
  · replace ⟨_, _, _, h⟩ := StateT.bind_some h
    exact (StateT.failure_some h).elim

theorem branch_merge_some [DecidableEq V]
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.merge .decider 1) inputs outputs))
  (h : (
    .assume (inputs.length = 3 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let inputL := inputs[1]'(by omega)
    let inputR := inputs[2]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseWithNames (inputs ++ outputs) λ
    | .async (AsyncOp.sink n) inputs' outputs' =>
      .assume (n > 0 ∧ inputs'.length = n ∧ outputs'.length = 0) λ _ => do
      if output ∈ inputs' then
        .apply "merge-sink" [
          .sink #v[decider],
          .sink #v[inputL],
          .sink #v[inputR],
          .sink (inputs'.erase output).toVector,
        ]
      else failure
    | .async (.steer flavor 1) inputs' outputs' =>
      .assume (inputs'.length = 2 ∧ outputs'.length = 1) λ h => do
      let decider' := inputs'[0]'(by omega)
      let input' := inputs'[1]'(by omega)
      let output' := outputs'[0]'(by omega)
      .assumeFromSameFork decider decider'
      if output = input' then
        if flavor then
          .apply "merge-steer-true" [
            .forward #v[inputR] #v[output'],
            .sink #v[decider, decider', inputL],
          ]
        else
          .apply "merge-steer-false" [
            .forward #v[inputL] #v[output'],
            .sink #v[decider, decider', inputR],
          ]
      else failure
    | .async (.fork n) inputs₀ outputs₀ =>
      .chooseWithNames (inputs₀ ++ outputs₀) λ
      | .async (.merge .decider 1) inputs' outputs' =>
        .assume (inputs'.length = 3 ∧ outputs'.length = 1) λ h => do
        let decider' := inputs'[0]'(by omega)
        let inputL' := inputs'[1]'(by omega)
        let inputR' := inputs'[2]'(by omega)
        let output' := outputs'[0]'(by omega)
        .assumeFromSameFork decider decider'
        .assumeFromSameFork inputL inputL'
        .assumeFromSameFork inputR inputR'
        .apply "merge-dedup" [
          .async (.fork n) inputs₀ outputs₀,
          .merge decider #v[inputL] #v[inputR] #v[.rename 0 output],
          .fork (.rename 0 output) #v[output, output'],
          .sink #v[decider', inputL', inputR'],
        ]
      | _ => failure
    | .async (.const v₁ 1) inputs₁ outputs₁ =>
      .assume (inputs₁.length = 1 ∧ outputs₁.length = 1) λ h => do
      let input₁ := inputs₁[0]'(by omega)
      let outputs₁ := outputs₁[0]'(by omega)
      .chooseWithNames (inputs ++ outputs) λ
      | .async (.const v₂ 1) inputs₂ outputs₂ =>
        .assume (inputs₂.length = 1 ∧ outputs₂.length = 1) λ h => do
        let input₂ := inputs₂[0]'(by omega)
        let outputs₂ := outputs₂[0]'(by omega)
        if inputL = outputs₁ ∧ inputR = outputs₂ then
          if v₁ = v₂ then
            .apply "merge-same-const" [
              .merge decider #v[input₁] #v[input₂] #v[.rename 0 input₁],
              .const v₁ (.rename 0 input₁) #v[output],
            ]
          else  if InterpConsts.toBool v₁ = some false ∧
            InterpConsts.toBool v₂ = some true then
            .apply "merge-true-false-const" [
              .forward #v[decider] #v[output],
              .sink #v[inputs₁[0]'(by omega)],
              .sink #v[inputs₂[0]'(by omega)],
            ]
          else failure
        else failure
      | _ => failure
    | _ => failure : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨decider, inputL, inputR, rfl⟩ := length_eq_three hlen₁
  obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hlen₂
  dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
  replace ⟨i₂, ap₂, hi₂, hap₂, h⟩ := RewriteM.chooseWithNames_some' h
  have hne₂₁ := ne_of_not_mem_singleton hi₂
  split at h
  · -- `merge-sink`
    replace ⟨⟨hk, hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain rfl := List.eq_nil_of_length_eq_zero hlen₄
    split at h
    · rename_i hmem
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .merge_sink hap hap₂ hne₂₁ hlen₃ hmem⟩
    · exact (StateT.failure_some h).elim
  · -- `merge-steer-*`
    replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨decider', input', rfl⟩ := length_eq_two hlen₃
    obtain ⟨output', rfl⟩ := List.length_eq_one_iff.mp hlen₄
    dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
    replace ⟨_, s₃, h₁, h⟩ := StateT.bind_some h
    obtain ⟨rfl, hfork⟩ := RewriteM.assumeFromSameFork_some' h₁
    split at h
    · rename_i heq
      subst heq
      split at h
      · rename_i hflavor
        subst hflavor
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        exact ⟨rfl, .merge_steer_true hap hap₂ hne₂₁ hfork⟩
      · rename_i hflavor
        obtain rfl : _ = false := by simpa using hflavor
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        exact ⟨rfl, .merge_steer_false hap hap₂ hne₂₁ hfork⟩
    · exact (StateT.failure_some h).elim
  · -- `merge-dedup`
    replace ⟨i₃, ap₃, hi₃, hap₃, h⟩ := RewriteM.chooseWithNames_some' h
    have ⟨hne₃₂, hne₃₁⟩ := ne_of_not_mem_pair hi₃
    split at h
    · replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
      obtain ⟨decider', inputL', inputR', rfl⟩ := length_eq_three hlen₃
      obtain ⟨output', rfl⟩ := List.length_eq_one_iff.mp hlen₄
      dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      replace ⟨_, s₃, h₁, h⟩ := StateT.bind_some h
      obtain ⟨rfl, hfork₁⟩ := RewriteM.assumeFromSameFork_some' h₁
      replace ⟨_, s₄, h₁, h⟩ := StateT.bind_some h
      obtain ⟨rfl, hfork₂⟩ := RewriteM.assumeFromSameFork_some' h₁
      replace ⟨_, s₅, h₁, h⟩ := StateT.bind_some h
      obtain ⟨rfl, hfork₃⟩ := RewriteM.assumeFromSameFork_some' h₁
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .merge_dedup hap hap₂ hap₃ hne₂₁ hne₃₁ hne₃₂ hfork₁ hfork₂ hfork₃⟩
    · exact (StateT.failure_some h).elim
  · -- `merge-same-const` and `merge-true-false-const`
    replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨input₁, rfl⟩ := List.length_eq_one_iff.mp hlen₃
    obtain ⟨output₁, rfl⟩ := List.length_eq_one_iff.mp hlen₄
    dsimp only [List.getElem_cons_zero] at h
    replace ⟨i₃, ap₃, hi₃, hap₃, h⟩ := RewriteM.chooseWithNames_some' h
    have ⟨hne₃₂, hne₃₁⟩ := ne_of_not_mem_pair hi₃
    split at h
    · replace ⟨⟨hlen₅, hlen₆⟩, h⟩ := RewriteM.assume_some h
      obtain ⟨input₂, rfl⟩ := List.length_eq_one_iff.mp hlen₅
      obtain ⟨output₂, rfl⟩ := List.length_eq_one_iff.mp hlen₆
      dsimp only [List.getElem_cons_zero] at h
      split at h
      · rename_i hcond
        obtain ⟨rfl, rfl⟩ := hcond
        split at h
        · rename_i heq
          subst heq
          obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
          exact ⟨rfl, .merge_same_const hap hap₂ hap₃ hne₂₁ hne₃₁ hne₃₂⟩
        · split at h
          · rename_i hbool
            obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
            exact ⟨rfl, .merge_true_false_const hap hap₂ hap₃ hne₂₁ hne₃₁ hne₃₂ hbool.1 hbool.2⟩
          · exact (StateT.failure_some h).elim
      · exact (StateT.failure_some h).elim
    · exact (StateT.failure_some h).elim
  · exact (StateT.failure_some h).elim

end Wavelet.Compile.DeadCodeElim.Extract
