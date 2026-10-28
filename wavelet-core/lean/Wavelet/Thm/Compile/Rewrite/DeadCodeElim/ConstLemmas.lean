import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! Helper lemmas for the `deadCodeElim` rules involving constants. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

/-- Values on a channel fed by a constant are all the constant. -/
theorem FromConst.eq_of_mem [Arity Op]
  {proc : Proc Op χ V m n} {chans : ChanMap χ V} {d : χ} {v : V}
  (hconst : FromConst proc.atoms d v) (hinv : ConstInv proc chans) :
    ∀ w ∈ chans d, w = v := by
  cases hconst with
  | const hmem hd => exact (hinv _ _ _ _ hmem _ hd).1
  | fork hfork hd hmem hx => exact (hinv _ _ _ _ hmem _ hx).2 _ _ hfork _ hd

namespace ConstLemmas

/-- A fresh name is different from the inputs of any atom. -/
theorem ne_of_fresh_input [Arity Op]
  {proc : Proc Op χ V m n} {i : Nat} {ap : AtomicProc Op χ V} {r x : χ}
  (hr : r ∉ proc.allNames) (hget : proc.atoms[i]? = some ap) (hx : x ∈ ap.inputs) : r ≠ x :=
  λ h => hr (h ▸ Proc.mem_allNames_of_input hget hx)

/-- A fresh name is different from the outputs of any atom. -/
theorem ne_of_fresh_output [Arity Op]
  {proc : Proc Op χ V m n} {i : Nat} {ap : AtomicProc Op χ V} {r x : χ}
  (hr : r ∉ proc.allNames) (hget : proc.atoms[i]? = some ap) (hx : x ∈ ap.outputs) : r ≠ x :=
  λ h => hr (h ▸ Proc.mem_allNames_of_output hget hx)

theorem ChanMap.pushed_swap [DecidableEq χ] {a b y : χ} {va vb : V} (h : a ≠ b) :
    ChanMap.pushed [a, b] [va, vb] y = ChanMap.pushed [b, a] [vb, va] y := by
  by_cases ha : a = y
  · subst ha; simp [Ne.symm h]
  · by_cases hb : b = y
    · subst hb; simp [ha]
    · simp [ha, hb]

/-- Point-wise facts about a pop by the environment. -/
theorem ChanMap.frame_pop_inv [DecidableEq χ] {chans chans' : ChanMap χ V} {x : χ} {w : V}
  (hpop : ∀ y, chans y = (if y = x then [w] else []) ++ chans' y) :
    chans x = w :: chans' x ∧ ∀ y, y ≠ x → chans' y = chans y :=
  ⟨by simpa using hpop x, λ y hy => by simpa [hy] using (hpop y).symm⟩

/-- Popping the head of a channel, in the form used by `frame_pop`. -/
theorem ChanMap.frame_pop_head [DecidableEq χ] {chans : ChanMap χ V} {x : χ} {w : V} {rest : List V}
  (hx : chans x = w :: rest) :
    ∃ chans' : ChanMap χ V, (∀ y, chans y = (if y = x then [w] else []) ++ chans' y) ∧
      chans' x = rest ∧ ∀ y, y ≠ x → chans' y = chans y := by
  refine ⟨λ y => if y = x then rest else chans y, ?_, by simp, λ y hy => by simp [hy]⟩
  intro y
  by_cases hy : y = x
  · subst hy; simp [hx]
  · simp [hy]

/-- Popping the head of a channel. -/
theorem ChanMap.pop_one [DecidableEq χ] {chans : ChanMap χ V} {x : χ} {w : V} {rest : List V}
  (hx : chans x = w :: rest) :
    ∃ chans' : ChanMap χ V, (∀ y, chans y = ChanMap.pushed [x] [w] y ++ chans' y) ∧
      chans' x = rest ∧ ∀ y, y ≠ x → chans' y = chans y := by
  refine ⟨λ y => if y = x then rest else chans y, ?_, by simp, λ y hy => by simp [hy]⟩
  intro y
  by_cases hy : y = x
  · subst hy; simp [hx]
  · simp [hy, Ne.symm hy]

/-- Popping the heads of two different channels. -/
theorem ChanMap.pop_two [DecidableEq χ] {chans : ChanMap χ V} {x₁ x₂ : χ} {w₁ w₂ : V}
  {rest₁ rest₂ : List V}
  (hne : x₁ ≠ x₂) (hx₁ : chans x₁ = w₁ :: rest₁) (hx₂ : chans x₂ = w₂ :: rest₂) :
    ∃ chans' : ChanMap χ V, (∀ y, chans y = ChanMap.pushed [x₁, x₂] [w₁, w₂] y ++ chans' y) ∧
      chans' x₁ = rest₁ ∧ chans' x₂ = rest₂ ∧ ∀ y, y ≠ x₁ → y ≠ x₂ → chans' y = chans y := by
  refine ⟨λ y => if y = x₁ then rest₁ else if y = x₂ then rest₂ else chans y, ?_,
    by simp, by simp [Ne.symm hne], λ y h₁ h₂ => by simp [h₁, h₂]⟩
  intro y
  by_cases h₁ : y = x₁
  · subst h₁; simp [hx₁, Ne.symm hne]
  · by_cases h₂ : y = x₂
    · subst h₂; simp [hx₂, h₁, Ne.symm h₁]
    · simp [h₁, h₂, Ne.symm h₁, Ne.symm h₂]

/-- Splits a list of values along a list of names `s ++ x :: t` of the same length. -/
theorem exists_split_of_length {ws : List α} {s t : List β} {x : β}
  (h : ws.length = (s ++ x :: t).length) :
    ∃ sv w tv, ws = sv ++ w :: tv ∧ sv.length = s.length ∧ tv.length = t.length := by
  induction s generalizing ws with
  | nil =>
    cases ws with
    | nil => simp at h
    | cons w tv => exact ⟨[], w, tv, rfl, rfl, by simpa using h⟩
  | cons a s ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      obtain ⟨sv, w', tv, rfl, h₁, h₂⟩ := ih (ws := ws) (by simpa using h)
      exact ⟨w :: sv, w', tv, rfl, by simp [h₁], h₂⟩

section Interp

variable {χ : Type u} {V : Type v} [InterpConsts V]

theorem AsyncOp.Interp.steer_mk {flavor b : Bool} {d x o : χ} {dv xv : V}
  (hb : InterpConsts.toBool dv = some b) :
    (AsyncOp.steer flavor 1).Interp (.mk [d, x] [o] [d, x] [dv, xv]
      (if b = flavor then [o] else []) (if b = flavor then [xv] else [])) (.steer flavor 1) := by
  by_cases h : b = flavor
  · simp only [h, ite_true]
    exact .interp_steer_true (inputs := [x]) (outputs := [o]) rfl rfl (h ▸ hb) rfl
  · simp only [h, ite_false]
    exact .interp_steer_false (inputs := [x]) (outputs := [o]) rfl rfl hb h

theorem AsyncOp.Interp.order_mk {k : Nat} [NeZero k] {xs : List χ} {y : χ} {w : V} {ws : List V}
  (hk : xs.length = k) (hk' : (w :: ws).length = k) :
    (AsyncOp.order k).Interp (.mk xs [y] xs (w :: ws) [y] [w]) (.order k) :=
  .interp_order hk hk'

end Interp

end ConstLemmas

end Wavelet.Compile.DeadCodeElim
