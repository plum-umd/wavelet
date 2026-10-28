import Wavelet.Dataflow.AsyncOp

/-! Inversion lemmas for `AsyncOp.Interp` on atoms with known names. -/

namespace Wavelet.Dataflow

open Semantics

variable {χ : Type u} {V : Type v} [InterpConsts V]
variable {inputs outputs : List χ} {inputVals outputVals : List V} {aop' : AsyncOp V}

theorem AsyncOp.Interp.forward_inv {x y : χ}
  (h : (AsyncOp.forward 1).Interp (.mk [x] [y] inputs inputVals outputs outputVals) aop')
  (hlen : inputs.length = inputVals.length) :
    aop' = .forward 1 ∧ inputs = [x] ∧ outputs = [y] ∧
    ∃ v, inputVals = [v] ∧ outputVals = [v] := by
  cases h
  match inputVals, hlen with
  | [v], _ => exact ⟨rfl, rfl, rfl, v, rfl, rfl⟩

theorem AsyncOp.Interp.switch_inv {d x y₁ y₂ : χ}
  (h : (AsyncOp.switch 1).Interp (.mk [d, x] [y₁, y₂] inputs inputVals outputs outputVals) aop')
  (hlen : inputs.length = inputVals.length) :
    aop' = .switch 1 ∧ inputs = [d, x] ∧
    ∃ dv xv b, inputVals = [dv, xv] ∧ InterpConsts.toBool dv = some b ∧
      outputs = (if b then [y₁] else [y₂]) ∧ outputVals = [xv] := by
  cases h with | interp_switch _ _ hb =>
  simp at hlen
  obtain ⟨xv, rfl⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨rfl, rfl, _, xv, _, rfl, hb, ?_, rfl⟩
  split <;> rfl

theorem AsyncOp.Interp.steer_inv {flavor : Bool} {d x y : χ}
  (h : (AsyncOp.steer flavor 1).Interp (.mk [d, x] [y] inputs inputVals outputs outputVals) aop')
  (hlen : inputs.length = inputVals.length) :
    aop' = .steer flavor 1 ∧ inputs = [d, x] ∧
    ∃ dv xv b, inputVals = [dv, xv] ∧ InterpConsts.toBool dv = some b ∧
      outputs = (if b = flavor then [y] else []) ∧
      outputVals = (if b = flavor then [xv] else []) := by
  cases h with
  | interp_steer_true _ _ hb heq =>
    simp at hlen
    obtain ⟨xv, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨rfl, rfl, _, xv, _, rfl, hb, by simp [heq], by simp [heq]⟩
  | interp_steer_false _ _ hb hne =>
    simp at hlen
    obtain ⟨xv, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨rfl, rfl, _, xv, _, rfl, hb, by simp [hne], by simp [hne]⟩

theorem AsyncOp.Interp.fork_inv {k : Nat} {x : χ} {ys : List χ}
  (h : (AsyncOp.fork k).Interp (.mk [x] ys inputs inputVals outputs outputVals) aop')
  (hlen : inputs.length = inputVals.length) :
    aop' = .fork k ∧ inputs = [x] ∧ outputs = ys ∧ ys.length = k ∧
    ∃ v, inputVals = [v] ∧ InterpConsts.isClonable v ∧ outputVals = List.replicate k v := by
  cases h with | interp_fork hk hclone =>
  exact ⟨rfl, rfl, rfl, hk, _, rfl, hclone, rfl⟩

theorem AsyncOp.Interp.const_inv {c : V} {k : Nat} {ins ys : List χ}
  (h : (AsyncOp.const c k).Interp (.mk ins ys inputs inputVals outputs outputVals) aop')
  (hlen : inputs.length = inputVals.length) :
    aop' = .const c k ∧ inputs = ins ∧ outputs = ys ∧ ys.length = k ∧
    (∃ a av, ins = [a] ∧ inputVals = [av]) ∧ outputVals = List.replicate k c := by
  cases h with | interp_const hk =>
  exact ⟨rfl, rfl, rfl, hk, ⟨_, _, rfl, rfl⟩, rfl⟩

theorem AsyncOp.Interp.order_inv {k : Nat} [NeZero k] {xs : List χ} {y : χ}
  (h : (AsyncOp.order k).Interp (.mk xs [y] inputs inputVals outputs outputVals) aop') :
    aop' = .order k ∧ inputs = xs ∧ outputs = [y] ∧ xs.length = k ∧
    ∃ v rest, inputVals = v :: rest ∧ outputVals = [v] := by
  cases h with | interp_order hk hk' =>
  match inputVals, hk' with
  | v :: rest, _ => exact ⟨rfl, rfl, rfl, hk, v, rest, rfl, rfl⟩
  | [], hk' => exact absurd hk'.symm (NeZero.ne k)

theorem AsyncOp.Interp.sink_inv {k : Nat} [NeZero k] {xs : List χ}
  (h : (AsyncOp.sink k).Interp (.mk xs [] inputs inputVals outputs outputVals) aop') :
    aop' = .sink k ∧ inputs = xs ∧ xs.length = k ∧ outputs = [] ∧ outputVals = [] := by
  cases h with | interp_sink hk =>
  exact ⟨rfl, rfl, hk, rfl, rfl⟩

theorem AsyncOp.Interp.inact_inv {k : Nat} {label : AsyncOp.Label χ V}
  (h : (AsyncOp.inact k).Interp label aop') : False := by
  cases h

theorem AsyncOp.Interp.merge_inv {st : AsyncOp.MergeState} {d l r o : χ}
  (h : (AsyncOp.merge st 1).Interp (.mk [d, l, r] [o] inputs inputVals outputs outputVals) aop')
  (hlen : inputs.length = inputVals.length) :
    (st = .popLeft ∧ aop' = .merge .decider 1 ∧ inputs = [l] ∧ outputs = [o] ∧
      ∃ v, inputVals = [v] ∧ outputVals = [v]) ∨
    (st = .popRight ∧ aop' = .merge .decider 1 ∧ inputs = [r] ∧ outputs = [o] ∧
      ∃ v, inputVals = [v] ∧ outputVals = [v]) ∨
    (st = .decider ∧ inputs = [d] ∧ outputs = [] ∧ outputVals = [] ∧
      ∃ dv b, inputVals = [dv] ∧ InterpConsts.toBool dv = some b ∧
        aop' = .merge (if b then .popRight else .popLeft) 1) := by
  cases h with
  | interp_merge_left =>
    simp at hlen
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen.symm
    exact .inl ⟨rfl, rfl, rfl, rfl, v, rfl, rfl⟩
  | interp_merge_right =>
    simp at hlen
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen.symm
    exact .inr (.inl ⟨rfl, rfl, rfl, rfl, v, rfl, rfl⟩)
  | interp_merge_decider _ _ hb =>
    exact .inr (.inr ⟨rfl, rfl, rfl, rfl, _, _, rfl, hb, rfl⟩)

theorem AsyncOp.Interp.inv_inv {flavor : Bool} {c : Option V} {d x y : χ}
  (h : (AsyncOp.inv flavor c).Interp (.mk [d, x] [y] inputs inputVals outputs outputVals) aop')
  (hlen : inputs.length = inputVals.length) :
    (c = none ∧ inputs = [x] ∧ outputs = [y] ∧
      ∃ v, inputVals = [v] ∧ InterpConsts.isClonable v ∧ outputVals = [v] ∧
        aop' = .inv flavor (some v)) ∨
    (∃ v, c = some v ∧ inputs = [d] ∧
      ∃ dv b, inputVals = [dv] ∧ InterpConsts.toBool dv = some b ∧
        ((b = flavor ∧ outputs = [y] ∧ outputVals = [v] ∧ aop' = .inv flavor (some v)) ∨
         (b ≠ flavor ∧ outputs = [] ∧ outputVals = [] ∧ aop' = .inv flavor none))) := by
  cases h with
  | interp_inv_init _ _ hclone =>
    exact .inl ⟨rfl, rfl, rfl, _, rfl, hclone, rfl, rfl⟩
  | interp_inv_true _ _ hb heq =>
    exact .inr ⟨_, rfl, rfl, _, _, rfl, hb, .inl ⟨heq, rfl, rfl, rfl⟩⟩
  | interp_inv_false _ _ hb hne =>
    exact .inr ⟨_, rfl, rfl, _, _, rfl, hb, .inr ⟨hne, rfl, rfl, rfl⟩⟩

end Wavelet.Dataflow
