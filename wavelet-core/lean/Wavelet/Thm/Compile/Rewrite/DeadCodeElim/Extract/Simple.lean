import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Extract.Basic

/-! Symbolic execution of the small top-level branches of `deadCodeElim`. -/

namespace Wavelet.Compile.DeadCodeElim.Extract

open Semantics Dataflow

variable {Op χ V : Type} [Arity Op] [DecidableEq χ] [Hashable χ] [InterpConsts V]

theorem branch_op_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {o : Op} {inputs : Vector (RewriteName χ) (Arity.ι o)}
  {outputs : Vector (RewriteName χ) (Arity.ω o)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.op o inputs outputs))
  (h : (
    .chooseWithNames (inputs.toList ++ outputs.toList) λ
    | .async (AsyncOp.order n) inputs₁ outputs₁ =>
      .assume (n > 0 ∧ inputs₁.length = n ∧ outputs₁.length = 1) λ h => do
      let input₁ := inputs₁[0]'(by omega)
      let output₁ := outputs₁[0]'(by omega)
      if output₁ ∈ inputs then
        .chooseWithNames (inputs.toList ++ outputs.toList) λ
        | .async (AsyncOp.order m) inputs₂ outputs₂ =>
          .assume (m > 0 ∧ inputs₂.length = m ∧ outputs₂.length = 1) λ h => do
          let output₂ := outputs₂[0]'(by omega)
          if output₂ ∈ inputs then
            let : NeZero (inputs₂ ++ inputs₁.tail).length := by
              constructor
              simp only [List.length_append]
              omega
            .apply "sync-order-order" [
              .op _ (inputs.replace output₁ input₁) outputs,
              .order (inputs₂ ++ inputs₁.tail).toVector output₂,
            ]
          else failure
        | _ => failure
      else failure
    | _ => failure : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨i₂, ap₂, hi₂, hap₂, h⟩ := RewriteM.chooseWithNames_some' h
  split at h
  · rename_i n _ inputs₁ outputs₁
    replace ⟨⟨hn, hlen₁, hlen₁'⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨output₁, rfl⟩ := List.length_eq_one_iff.mp hlen₁'
    obtain ⟨input₁, rest₁, rfl⟩ := List.exists_cons_of_length_pos (hlen₁ ▸ hn)
    dsimp only [List.getElem_cons_zero, List.tail_cons] at h
    split at h
    · rename_i hmem₁
      replace ⟨i₃, ap₃, hi₃, hap₃, h⟩ := RewriteM.chooseWithNames_some' h
      split at h
      · rename_i k _ inputs₂ outputs₂
        replace ⟨⟨hk, hlen₂, hlen₂'⟩, h⟩ := RewriteM.assume_some h
        obtain ⟨output₂, rfl⟩ := List.length_eq_one_iff.mp hlen₂'
        dsimp only [List.getElem_cons_zero] at h
        split at h
        · rename_i hmem₂
          obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
          have ⟨hne₃₂, hne₃₁⟩ := ne_of_not_mem_pair hi₃
          haveI : NeZero (inputs₂ ++ rest₁).length := ⟨by rw [List.length_append]; omega⟩
          exact ⟨rfl, .sync_order_order (rest₁ := rest₁) hap hap₂ hap₃ (ne_of_not_mem_singleton hi₂)
            hne₃₁ hne₃₂ hlen₁ hlen₂ hmem₁ hmem₂⟩
        · exact (StateT.failure_some h).elim
      · exact (StateT.failure_some h).elim
    · exact (StateT.failure_some h).elim
  · exact (StateT.failure_some h).elim

theorem branch_forward_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.forward 1) inputs outputs))
  (h : (
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    let input := inputs[0]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseWithNames [input, output] λ
    | .async aop inputs' outputs' => do
      if output ∈ inputs' then
        .apply "fold-forward-aop-receiver" [.async aop (inputs'.replace output input) outputs']
      else if input ∈ outputs' then
        .apply "fold-forward-aop-sender" [.async aop inputs' (outputs'.replace input output)]
      else failure
    | .op op inputs' outputs' => do
      if output ∈ inputs' then
        .apply "fold-forward-op-receiver" [.op op (inputs'.replace output input) outputs']
      else if input ∈ outputs' then
        .apply "fold-forward-op-sender" [.op op inputs' (outputs'.replace input output)]
      else failure : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨input, rfl⟩ := List.length_eq_one_iff.mp hlen₁
  obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hlen₂
  dsimp only [List.getElem_cons_zero] at h
  replace ⟨i₂, ap₂, hi₂, hap₂, h⟩ := RewriteM.chooseWithNames_some' h
  have hne := ne_of_not_mem_singleton hi₂
  split at h
  · split at h
    · rename_i hmem
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .fold_forward_aop_receiver hap hap₂ hne hmem⟩
    · split at h
      · rename_i hnmem hmem
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        exact ⟨rfl, .fold_forward_aop_sender hap hap₂ hne hnmem hmem⟩
      · exact (StateT.failure_some h).elim
  · split at h
    · rename_i hmem
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .fold_forward_op_receiver hap hap₂ hne hmem⟩
    · split at h
      · rename_i hnmem hmem
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        exact ⟨rfl, .fold_forward_op_sender hap hap₂ hne hnmem hmem⟩
      · exact (StateT.failure_some h).elim

theorem branch_switch_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.switch 1) inputs outputs))
  (h : (
    .assume (inputs.length = 2 ∧ outputs.length = 2) λ h => do
    let decider := inputs[0]'(by omega)
    let input := inputs[1]'(by omega)
    let output₁ := outputs[0]'(by omega)
    let output₂ := outputs[1]'(by omega)
    .chooseWithNames [output₁, output₂] λ
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if output₁ = sink then
        .apply "switch-sink-left" [.steer false decider #v[input] #v[output₂]]
      else if output₂ = sink then
        .apply "switch-sink-right" [.steer true decider #v[input] #v[output₁]]
      else failure
    | _ => failure : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨decider, input, rfl⟩ := length_eq_two hlen₁
  obtain ⟨output₁, output₂, rfl⟩ := length_eq_two hlen₂
  dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
  replace ⟨i₂, ap₂, hi₂, hap₂, h⟩ := RewriteM.chooseWithNames_some' h
  split at h
  · replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨sink, rfl⟩ := List.length_eq_one_iff.mp hlen₃
    obtain rfl := List.eq_nil_of_length_eq_zero hlen₄
    dsimp only [List.getElem_cons_zero] at h
    split at h
    · rename_i heq
      subst heq
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .switch_sink_left hap hap₂ (ne_of_not_mem_singleton hi₂)⟩
    · split at h
      · rename_i hne heq
        subst heq
        obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
        exact ⟨rfl, .switch_sink_right hap hap₂ (ne_of_not_mem_singleton hi₂) hne⟩
      · exact (StateT.failure_some h).elim
  · exact (StateT.failure_some h).elim

theorem branch_fork_zero_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.fork 0) inputs outputs))
  (h : (
    .assume (inputs.length = 1 ∧ outputs.length = 0) λ _ => do
    .apply "fork-0" [.sink inputs.toVector] : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨input, rfl⟩ := List.length_eq_one_iff.mp hlen₁
  obtain rfl := List.eq_nil_of_length_eq_zero hlen₂
  obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
  exact ⟨rfl, .fork_0 hap⟩

theorem branch_fork_one_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.fork 1) inputs outputs))
  (h : (
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    .apply "fork-1" [.forward #v[inputs[0]] #v[outputs[0]]] : Rewrite Op χ V)
    s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨input, rfl⟩ := List.length_eq_one_iff.mp hlen₁
  obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hlen₂
  obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
  exact ⟨rfl, .fork_1 hap⟩

theorem branch_fork_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {n : Nat} {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.fork n) inputs outputs))
  (h : (
    .assume (inputs.length = 1 ∧ outputs.length = n) λ h => do
    let input := inputs[0]'(by omega)
    .chooseWithNames (inputs ++ outputs) λ
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if sink ∈ outputs then
        .apply "fork-sink" [.fork input (outputs.erase sink).toVector]
      else failure
    | .async (.fork m) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = m) λ h => do
      let input' := inputs'[0]'(by omega)
      if input' ∈ outputs then
        .apply "fork-fork" [.fork input (outputs.erase input' ++ outputs').toVector]
      else failure
    | _ => failure : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨input, rfl⟩ := List.length_eq_one_iff.mp hlen₁
  dsimp only [List.getElem_cons_zero] at h
  replace ⟨i₂, ap₂, hi₂, hap₂, h⟩ := RewriteM.chooseWithNames_some' h
  have hne := ne_of_not_mem_singleton hi₂
  split at h
  · replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨sink, rfl⟩ := List.length_eq_one_iff.mp hlen₃
    obtain rfl := List.eq_nil_of_length_eq_zero hlen₄
    dsimp only [List.getElem_cons_zero] at h
    split at h
    · rename_i hmem
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .fork_sink hap hap₂ hne hlen₂ hmem⟩
    · exact (StateT.failure_some h).elim
  · replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨input', rfl⟩ := List.length_eq_one_iff.mp hlen₃
    dsimp only [List.getElem_cons_zero] at h
    split at h
    · rename_i hmem
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .fork_fork hap hap₂ hne hlen₂ hlen₄ hmem⟩
    · exact (StateT.failure_some h).elim
  · exact (StateT.failure_some h).elim

theorem branch_order_one_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.order 1) inputs outputs))
  (h : (
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    let input := inputs[0]'(by omega)
    let output := outputs[0]'(by omega)
    .apply "order-1" [.forward #v[input] #v[output]] : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨input, rfl⟩ := List.length_eq_one_iff.mp hlen₁
  obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hlen₂
  obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
  exact ⟨rfl, .order_1 hap⟩

theorem branch_const_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {v : V} {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.const v 1) inputs outputs))
  (h : (
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    let act := inputs[0]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseWithNames (inputs ++ outputs) λ
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if output = sink then
        .apply "const-sink" [.sink #v[act]]
      else failure
    | _ => failure : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain ⟨act, rfl⟩ := List.length_eq_one_iff.mp hlen₁
  obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hlen₂
  dsimp only [List.getElem_cons_zero] at h
  replace ⟨i₂, ap₂, hi₂, hap₂, h⟩ := RewriteM.chooseWithNames_some' h
  split at h
  · replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain ⟨sink, rfl⟩ := List.length_eq_one_iff.mp hlen₃
    obtain rfl := List.eq_nil_of_length_eq_zero hlen₄
    dsimp only [List.getElem_cons_zero] at h
    split at h
    · rename_i heq
      subst heq
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .const_sink hap hap₂ (ne_of_not_mem_singleton hi₂)⟩
    · exact (StateT.failure_some h).elim
  · exact (StateT.failure_some h).elim

theorem branch_inact_some
  {aps : AtomicProcs Op (RewriteName χ) V} {i₁ : Nat}
  {n : Nat} {inputs outputs : List (RewriteName χ)}
  {s s' : RewriteState Op χ V} {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  (hs : s.aps = aps) (hm : s.matched = [i₁])
  (hap : aps[i₁]? = some (.async (.inact n) inputs outputs))
  (h : (
    .assume (n > 0 ∧ inputs.length = 0 ∧ outputs.length = n) λ _ => do
    .chooseWithNames outputs λ
    | .async (AsyncOp.sink m) inputs' outputs' =>
      .assume (inputs'.length = m ∧ outputs'.length = 0) λ _ => do
      if ¬ outputs.Disjoint inputs' then
        .apply "inact-sink" [
          .inact (outputs.removeAll inputs').toVector,
          .sink (inputs'.removeAll outputs).toVector,
        ]
      else failure
    | _ => failure : Rewrite Op χ V) s = some ((name, res), s')) :
    s'.aps = aps ∧ DCEMatch aps s'.matched name res := by
  obtain ⟨aps', cta, matched, dr⟩ := s
  dsimp only at hs hm
  subst hs hm
  replace ⟨⟨hn, hlen₁, hlen₂⟩, h⟩ := RewriteM.assume_some h
  obtain rfl := List.eq_nil_of_length_eq_zero hlen₁
  replace ⟨i₂, ap₂, hi₂, hap₂, h⟩ := RewriteM.chooseWithNames_some' h
  split at h
  · replace ⟨⟨hlen₃, hlen₄⟩, h⟩ := RewriteM.assume_some h
    obtain rfl := List.eq_nil_of_length_eq_zero hlen₄
    split at h
    · rename_i hndisj
      obtain ⟨rfl, rfl, rfl⟩ := RewriteM.apply_some' h
      exact ⟨rfl, .inact_sink hap hap₂ (ne_of_not_mem_singleton hi₂) hn hlen₂ hlen₃ hndisj⟩
    · exact (StateT.failure_some h).elim
  · exact (StateT.failure_some h).elim

end Wavelet.Compile.DeadCodeElim.Extract
