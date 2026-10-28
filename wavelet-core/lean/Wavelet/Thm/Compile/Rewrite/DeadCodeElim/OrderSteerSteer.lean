import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! `order-steer-steer`: an order of two steers with the same decider can be moved up. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

namespace OrderSteerSteer

/-- Values passed by a steer of the given flavor, given the deciders and the inputs. -/
private def passed [InterpConsts V] (flavor : Bool) (ds xs : List V) : List V :=
  (ds.zip xs).filterMap (λ (d, x) => if InterpConsts.toBool d = some flavor then some x else none)

@[simp]
private theorem passed_nil_left [InterpConsts V] {flavor : Bool} {xs : List V} :
    passed flavor [] xs = [] := by
  simp [passed]

@[simp]
private theorem passed_nil_right [InterpConsts V] {flavor : Bool} {ds : List V} :
    passed flavor ds [] = [] := by
  simp [passed]

private theorem passed_cons [InterpConsts V] {flavor : Bool} {d x : V} {ds xs : List V} :
    passed flavor (d :: ds) (x :: xs) =
      (if InterpConsts.toBool d = some flavor then [x] else []) ++ passed flavor ds xs := by
  by_cases h : InterpConsts.toBool d = some flavor <;> simp [passed, h]

private theorem passed_append_single [InterpConsts V] {flavor : Bool} {d x : V} {ds xs : List V}
  (hlen : ds.length = xs.length) :
    passed flavor (ds ++ [d]) (xs ++ [x]) =
      passed flavor ds xs ++ (if InterpConsts.toBool d = some flavor then [x] else []) := by
  by_cases h : InterpConsts.toBool d = some flavor <;> simp [passed, List.zip_append hlen, h]

private theorem passed_single [InterpConsts V] {flavor b : Bool} {d x : V}
  (hb : InterpConsts.toBool d = some b) :
    (if InterpConsts.toBool d = some flavor then [x] else []) = (if b = flavor then [x] else []) := by
  simp [hb]

/-- A steer fires with a known decider. -/
private theorem steer_interp [InterpConsts V] {flavor b : Bool} {d x y : χ} {dv xv : V}
  (hb : InterpConsts.toBool dv = some b) :
    (AsyncOp.steer flavor 1).Interp
      (.mk [d, x] [y] [d, x] [dv, xv] (if b = flavor then [y] else []) (if b = flavor then [xv] else []))
      (.steer flavor 1) := by
  by_cases h : b = flavor
  · simp only [h, if_true]
    exact .interp_steer_true rfl rfl (h ▸ hb) rfl
  · simp only [h, if_false]
    exact .interp_steer_false rfl rfl hb h

private theorem pushed_single [DecidableEq χ] {x y : χ} {v : V} :
    ChanMap.pushed [x] [v] y = if y = x then [v] else [] := by
  by_cases h : y = x
  · subst h; simp
  · simp [h, Ne.symm h]

private theorem pushed_ite [DecidableEq χ] {c : Prop} [Decidable c] {x y : χ} {v : V} :
    ChanMap.pushed (if c then [x] else []) (if c then [v] else []) y =
      if y = x ∧ c then [v] else [] := by
  by_cases hc : c
  · simp only [hc, if_true, and_true, pushed_single]
  · simp [hc]

/-- Pushing copies of one value to distinct names. -/
private theorem pushed_of_forall_eq [DecidableEq χ] {names : List χ} {vals : List V} {y : χ} {v : V}
  (hnd : names.Nodup) (hlen : names.length = vals.length) (hv : ∀ w ∈ vals, w = v)
  (hy : y ∈ names) : ChanMap.pushed names vals y = [v] := by
  induction names generalizing vals with
  | nil => simp at hy
  | cons x names ih =>
    cases vals with
    | nil => simp at hlen
    | cons w vals =>
      have ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      rw [ChanMap.pushed_cons]
      by_cases hxy : x = y
      · subst hxy
        rw [ChanMap.pushed_not_mem hx, hv w (by simp)]
        simp
      · have hy' : y ∈ names := by
          rcases List.mem_cons.mp hy with h | h
          · exact absurd h.symm hxy
          · exact h
        rw [ih hnd' (by simpa using hlen) (λ w' hw' => hv w' (by simp [hw'])) hy']
        simp [hxy]

/-- Distinctness of the channel names (in both directions, for `simp`). -/
private def Distinct (d₁ d₂ in₁ in₂ oi₁ oi₂ out : χ) : Prop :=
  (d₁ ≠ d₂ ∧ d₁ ≠ in₁ ∧ d₁ ≠ in₂ ∧ d₁ ≠ oi₁ ∧ d₁ ≠ oi₂ ∧
    d₂ ≠ in₁ ∧ d₂ ≠ in₂ ∧ d₂ ≠ oi₁ ∧ d₂ ≠ oi₂ ∧
    in₁ ≠ in₂ ∧ in₁ ≠ oi₁ ∧ in₁ ≠ oi₂ ∧ in₂ ≠ oi₁ ∧ in₂ ≠ oi₂ ∧ oi₁ ≠ oi₂ ∧
    out ≠ d₁ ∧ out ≠ d₂ ∧ out ≠ oi₁ ∧ out ≠ oi₂) ∧
  (d₂ ≠ d₁ ∧ in₁ ≠ d₁ ∧ in₂ ≠ d₁ ∧ oi₁ ≠ d₁ ∧ oi₂ ≠ d₁ ∧
    in₁ ≠ d₂ ∧ in₂ ≠ d₂ ∧ oi₁ ≠ d₂ ∧ oi₂ ≠ d₂ ∧
    in₂ ≠ in₁ ∧ oi₁ ≠ in₁ ∧ oi₂ ≠ in₁ ∧ oi₁ ≠ in₂ ∧ oi₂ ≠ in₂ ∧ oi₂ ≠ oi₁ ∧
    d₁ ≠ out ∧ d₂ ≠ out ∧ oi₁ ≠ out ∧ oi₂ ≠ out)

private theorem distinct_of {d₁ d₂ in₁ in₂ oi₁ oi₂ out : χ}
  (h₁ : d₁ ≠ d₂) (h₂ : d₁ ≠ in₁) (h₃ : d₁ ≠ in₂) (h₄ : d₁ ≠ oi₁) (h₅ : d₁ ≠ oi₂)
  (h₆ : d₂ ≠ in₁) (h₇ : d₂ ≠ in₂) (h₈ : d₂ ≠ oi₁) (h₉ : d₂ ≠ oi₂)
  (h₁₀ : in₁ ≠ in₂) (h₁₁ : in₁ ≠ oi₁) (h₁₂ : in₁ ≠ oi₂) (h₁₃ : in₂ ≠ oi₁) (h₁₄ : in₂ ≠ oi₂)
  (h₁₅ : oi₁ ≠ oi₂) (h₁₆ : out ≠ d₁) (h₁₇ : out ≠ d₂) (h₁₈ : out ≠ oi₁) (h₁₉ : out ≠ oi₂) :
    Distinct d₁ d₂ in₁ in₂ oi₁ oi₂ out :=
  ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩,
    ⟨h₁.symm, h₂.symm, h₃.symm, h₄.symm, h₅.symm, h₆.symm, h₇.symm, h₈.symm, h₉.symm,
      h₁₀.symm, h₁₁.symm, h₁₂.symm, h₁₃.symm, h₁₄.symm, h₁₅.symm, h₁₆.symm, h₁₇.symm,
      h₁₈.symm, h₁₉.symm⟩⟩

private theorem ne_of_disjoint {l₁ l₂ : List χ} {a b : χ}
  (h : l₁.Disjoint l₂) (ha : a ∈ l₁) (hb : b ∈ l₂) : a ≠ b :=
  λ e => h ha (e ▸ hb)

variable [Arity Op] [DecidableEq χ] [InterpConsts V]

/-- The replacement atoms. -/
private abbrev newAtoms (flavor : Bool) (d₁ d₂ in₁ in₂ oi₁ out : χ) : AtomicProcs Op χ V :=
  [.order #v[in₁, in₂] oi₁, .steer flavor d₁ #v[oi₁] #v[out], .sink #v[d₂]]

/-- The replacement atoms process one position: the order, the steer, and the sink fire. -/
private theorem fire_three {flavor b : Bool} {d₁ d₂ in₁ in₂ oi₁ out : χ}
  {chans : ChanMap χ V} {x₁ x₂ dv : V} {R₁ R₂ D₁ D₂ : List V}
  (hd₁d₂ : d₁ ≠ d₂) (hd₁i₁ : d₁ ≠ in₁) (hd₁i₂ : d₁ ≠ in₂) (hd₁o : d₁ ≠ oi₁)
  (hd₂i₁ : d₂ ≠ in₁) (hd₂i₂ : d₂ ≠ in₂)
  (hi₁i₂ : in₁ ≠ in₂) (hi₁o : in₁ ≠ oi₁) (hi₂o : in₂ ≠ oi₁) (hout₂ : out ≠ d₂)
  (hin₁ : chans in₁ = x₁ :: R₁) (hin₂ : chans in₂ = x₂ :: R₂)
  (hd₁ : chans d₁ = dv :: D₁) (hd₂ : chans d₂ = dv :: D₂) (hoi₁ : chans oi₁ = [])
  (hb : InterpConsts.toBool dv = some b) :
    LocalTauStar (newAtoms (Op := Op) flavor d₁ d₂ in₁ in₂ oi₁ out) chans
      (newAtoms flavor d₁ d₂ in₁ in₂ oi₁ out)
      (λ y => (if y = in₁ then R₁ else if y = in₂ then R₂ else
        if y = d₁ then D₁ else if y = d₂ then D₂ else chans y) ++
        (if y = out ∧ b = flavor then [x₁] else [])) := by
  -- The order
  have hstep₁ := LocalTauStar.async_list_mem
    (L := newAtoms (Op := Op) flavor d₁ d₂ in₁ in₂ oi₁ out)
    (aop := .order 2) (allInputs := [in₁, in₂]) (allOutputs := [oi₁])
    (inputs := [in₁, in₂]) (inputVals := [x₁, x₂]) (outputs := [oi₁]) (outputVals := [x₁])
    (chans := chans)
    (chans' := λ y => if y = in₁ then R₁ else if y = in₂ then R₂ else chans y)
    (by simp [AtomicProc.order]) (.interp_order (k := 2) rfl rfl) rfl rfl
    (by
      intro y
      by_cases h₁ : in₁ = y
      · subst h₁; simp [hin₁, Ne.symm hi₁i₂]
      · by_cases h₂ : in₂ = y
        · subst h₂; simp [hin₂, hi₁i₂, Ne.symm hi₁i₂]
        · simp [h₁, h₂, Ne.symm h₁, Ne.symm h₂])
  have hstep₁ := hstep₁.eq_rhs rfl (by funext y; rw [pushed_single] :
    _ = λ y => (if y = in₁ then R₁ else if y = in₂ then R₂ else chans y) ++
      (if y = oi₁ then [x₁] else []))
  -- The steer
  have hstep₂ := LocalTauStar.async_list_mem
    (L := newAtoms (Op := Op) flavor d₁ d₂ in₁ in₂ oi₁ out)
    (aop := .steer flavor 1) (allInputs := [d₁, oi₁]) (allOutputs := [out])
    (inputs := [d₁, oi₁]) (inputVals := [dv, x₁])
    (outputs := if b = flavor then [out] else []) (outputVals := if b = flavor then [x₁] else [])
    (chans := λ y => (if y = in₁ then R₁ else if y = in₂ then R₂ else chans y) ++
      (if y = oi₁ then [x₁] else []))
    (chans' := λ y => if y = in₁ then R₁ else if y = in₂ then R₂ else
      if y = d₁ then D₁ else chans y)
    (by simp [AtomicProc.steer]) (steer_interp hb) rfl (by split <;> rfl)
    (by
      intro y
      by_cases h₁ : d₁ = y
      · subst h₁; simp [hd₁, hd₁i₁, hd₁i₂, hd₁o, Ne.symm hd₁o]
      · by_cases h₂ : oi₁ = y
        · subst h₂; simp [hoi₁, Ne.symm hi₁o, Ne.symm hi₂o, Ne.symm hd₁o, hd₁o]
        · simp [h₁, h₂, Ne.symm h₁, Ne.symm h₂])
  have hstep₂ := hstep₂.eq_rhs rfl (by funext y; rw [pushed_ite] :
    _ = λ y => (if y = in₁ then R₁ else if y = in₂ then R₂ else
      if y = d₁ then D₁ else chans y) ++ (if y = out ∧ b = flavor then [x₁] else []))
  -- The sink
  have hstep₃ := LocalTauStar.async_list_mem
    (L := newAtoms (Op := Op) flavor d₁ d₂ in₁ in₂ oi₁ out)
    (aop := .sink 1) (allInputs := [d₂]) (allOutputs := [])
    (inputs := [d₂]) (inputVals := [dv]) (outputs := []) (outputVals := [])
    (chans := λ y => (if y = in₁ then R₁ else if y = in₂ then R₂ else
      if y = d₁ then D₁ else chans y) ++ (if y = out ∧ b = flavor then [x₁] else []))
    (chans' := λ y => (if y = in₁ then R₁ else if y = in₂ then R₂ else
      if y = d₁ then D₁ else if y = d₂ then D₂ else chans y) ++
      (if y = out ∧ b = flavor then [x₁] else []))
    (by simp [AtomicProc.sink]) (.interp_sink rfl) rfl rfl
    (by
      intro y
      by_cases h₁ : d₂ = y
      · subst h₁; simp [hd₂, hd₂i₁, hd₂i₂, Ne.symm hd₁d₂, Ne.symm hout₂]
      · simp [h₁, Ne.symm h₁])
  exact (hstep₁.trans hstep₂).trans (hstep₃.eq_rhs rfl (by funext y; simp))

/--
The simulation invariant. The rewritten graph processes a position (of the
deciders) only after both original steers have processed it.
- `X₁`/`X₂` are the values of `in₁`/`in₂` consumed by the faster original steer only,
  and `P₁`/`P₂` the corresponding decider values (one side is always empty).
- `S` and `B` are the values in `oi₁`/`oi₂` from positions processed by both steers;
  the rewritten graph has already output `S` to `out`.
-/
private structure Inv (flavor : Bool) (d₁ d₂ in₁ in₂ oi₁ oi₂ out : χ)
    (chans₀ chans₁ : ChanMap χ V) (X₁ X₂ P₁ P₂ S B : List V) : Prop where
  len_x₁ : X₁.length = (chans₀ d₂).length - (chans₀ d₁).length
  len_x₂ : X₂.length = (chans₀ d₁).length - (chans₀ d₂).length
  len_p₁ : P₁.length = X₁.length
  len_p₂ : P₂.length = X₂.length
  len_sb : S.length = B.length
  ch_d₁ : chans₁ d₁ = P₁ ++ chans₀ d₁
  ch_d₂ : chans₁ d₂ = P₂ ++ chans₀ d₂
  d_eq : P₁ ++ chans₀ d₁ = P₂ ++ chans₀ d₂
  ch_oi₁ : chans₀ oi₁ = S ++ passed flavor P₁ X₁
  ch_oi₂ : chans₀ oi₂ = B ++ passed flavor P₂ X₂
  ch_oi₁' : chans₁ oi₁ = []
  ch_oi₂' : chans₁ oi₂ = []
  other : ∀ y, y ≠ d₁ → y ≠ d₂ → y ≠ oi₁ → y ≠ oi₂ →
    chans₁ y = (if y = in₁ then X₁ else []) ++ (if y = in₂ then X₂ else []) ++
      chans₀ y ++ (if y = out then S else [])

section Inv

variable {flavor : Bool} {d₁ d₂ in₁ in₂ oi₁ oi₂ out : χ} {X₁ X₂ P₁ P₂ S B : List V}

private theorem inv_init :
    Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out (.empty : ChanMap χ V) .empty [] [] [] [] [] [] :=
  ⟨by simp, by simp, rfl, rfl, rfl, rfl, rfl, rfl, by simp, by simp, rfl, rfl,
    λ y _ _ _ _ => by simp⟩

private theorem inv_empty {chans₁ : ChanMap χ V}
  (hinv : Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out .empty chans₁ X₁ X₂ P₁ P₂ S B) :
    chans₁ = .empty := by
  have hX₁ : X₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hinv.len_x₁)
  have hX₂ : X₂ = [] := List.eq_nil_of_length_eq_zero (by simpa using hinv.len_x₂)
  have hP₁ : P₁ = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len_p₁, hX₁]; rfl)
  have hP₂ : P₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len_p₂, hX₂]; rfl)
  have hS : S = [] := by
    have := hinv.ch_oi₁
    simp only [ChanMap.empty_apply, hP₁, passed_nil_left, List.append_nil] at this
    exact this.symm
  funext y
  by_cases h₁ : y = d₁
  · subst h₁; simp [hinv.ch_d₁, hP₁]
  · by_cases h₂ : y = d₂
    · subst h₂; simp [hinv.ch_d₂, hP₂]
    · by_cases h₃ : y = oi₁
      · subst h₃; simp [hinv.ch_oi₁']
      · by_cases h₄ : y = oi₂
        · subst h₄; simp [hinv.ch_oi₂']
        · simp [hinv.other y h₁ h₂ h₃ h₄, hX₁, hX₂, hS]

private theorem inv_frame_pop {chans₀ chans₀' chans₁ : ChanMap χ V} {x : χ} {v : V}
  (hinv : Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out chans₀ chans₁ X₁ X₂ P₁ P₂ S B)
  (hxd₁ : x ≠ d₁) (hxd₂ : x ≠ d₂) (hxi₁ : x ≠ in₁) (hxi₂ : x ≠ in₂)
  (hxo₁ : x ≠ oi₁) (hxo₂ : x ≠ oi₂)
  (hpop : ∀ y, chans₀ y = (if y = x then [v] else []) ++ chans₀' y) :
    ∃ chans₁', (∀ y, chans₁ y = (if y = x then [v] else []) ++ chans₁' y) ∧
      Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out chans₀' chans₁' X₁ X₂ P₁ P₂ S B := by
  have hsame : ∀ y, y ≠ x → chans₀' y = chans₀ y := λ y hy => by simp [hpop y, hy]
  have hx : chans₁ x = v :: (chans₀' x ++ (if x = out then S else [])) := by
    rw [hinv.other x hxd₁ hxd₂ hxo₁ hxo₂, hpop x]
    simp [hxi₁, hxi₂]
  refine ⟨λ y => if y = x then (chans₁ y).tail else chans₁ y, ?_, ?_⟩
  · intro y
    by_cases hy : y = x
    · subst hy; simp [hx]
    · simp [hy]
  · have e₁ := hsame d₁ (Ne.symm hxd₁)
    have e₂ := hsame d₂ (Ne.symm hxd₂)
    have e₃ := hsame oi₁ (Ne.symm hxo₁)
    have e₄ := hsame oi₂ (Ne.symm hxo₂)
    refine ⟨?_, ?_, hinv.len_p₁, hinv.len_p₂, hinv.len_sb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e₁, e₂]; exact hinv.len_x₁
    · rw [e₁, e₂]; exact hinv.len_x₂
    · simp [Ne.symm hxd₁, e₁, hinv.ch_d₁]
    · simp [Ne.symm hxd₂, e₂, hinv.ch_d₂]
    · rw [e₁, e₂]; exact hinv.d_eq
    · rw [e₃]; exact hinv.ch_oi₁
    · rw [e₄]; exact hinv.ch_oi₂
    · simp [Ne.symm hxo₁, hinv.ch_oi₁']
    · simp [Ne.symm hxo₂, hinv.ch_oi₂']
    · intro y h₁ h₂ h₃ h₄
      by_cases hy : y = x
      · subst hy; simp [hx, hxi₁, hxi₂]
      · simp only [hy, if_false]
        rw [hinv.other y h₁ h₂ h₃ h₄, hsame y hy]

private theorem inv_frame_push {chans₀ chans₁ : ChanMap χ V} {outs : List χ} {vals : List V}
  (hinv : Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out chans₀ chans₁ X₁ X₂ P₁ P₂ S B)
  (hd : ChanMap.pushed outs vals d₁ = ChanMap.pushed outs vals d₂)
  (ho₁ : oi₁ ∉ outs) (ho₂ : oi₂ ∉ outs) (hout : out ∉ outs) :
    Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out
      (λ y => chans₀ y ++ ChanMap.pushed outs vals y)
      (λ y => chans₁ y ++ ChanMap.pushed outs vals y) X₁ X₂ P₁ P₂ S B := by
  have p₁ := ChanMap.pushed_not_mem (vals := vals) ho₁
  have p₂ := ChanMap.pushed_not_mem (vals := vals) ho₂
  have p₃ := ChanMap.pushed_not_mem (vals := vals) hout
  refine ⟨?_, ?_, hinv.len_p₁, hinv.len_p₂, hinv.len_sb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, hd]; have := hinv.len_x₁; omega
  · simp only [List.length_append, hd]; have := hinv.len_x₂; omega
  · simp only [hinv.ch_d₁, List.append_assoc]
  · simp only [hinv.ch_d₂, List.append_assoc]
  · simp only [← List.append_assoc, hinv.d_eq, hd]
  · simp only [p₁, List.append_nil, hinv.ch_oi₁]
  · simp only [p₂, List.append_nil, hinv.ch_oi₂]
  · simp only [p₁, List.append_nil, hinv.ch_oi₁']
  · simp only [p₂, List.append_nil, hinv.ch_oi₂']
  · intro y h₁ h₂ h₃ h₄
    simp only [hinv.other y h₁ h₂ h₃ h₄, List.append_assoc]
    by_cases hy : y = out
    · subst hy; simp [p₃]
    · simp [hy]

private theorem inv_step_order {chans₀ chans₀' chans₁ : ChanMap χ V} {v₁ v₂ : V}
  (hD : Distinct d₁ d₂ in₁ in₂ oi₁ oi₂ out)
  (hinv : Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out chans₀ chans₁ X₁ X₂ P₁ P₂ S B)
  (hpop : ∀ y, chans₀ y = ChanMap.pushed [oi₁, oi₂] [v₁, v₂] y ++ chans₀' y) :
    ∃ S' B', Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out
      (λ y => chans₀' y ++ ChanMap.pushed [out] [v₁] y) chans₁ X₁ X₂ P₁ P₂ S' B' := by
  unfold Distinct at hD
  have hoi₁ : chans₀ oi₁ = v₁ :: chans₀' oi₁ := by simp [hpop oi₁, hD]
  have hoi₂ : chans₀ oi₂ = v₂ :: chans₀' oi₂ := by simp [hpop oi₂, hD]
  have hsame : ∀ y, y ≠ oi₁ → y ≠ oi₂ → chans₀' y = chans₀ y := λ y h₁ h₂ => by
    simp [hpop y, Ne.symm h₁, Ne.symm h₂]
  -- The order can only fire if `S` is non-empty.
  have hne : S ≠ [] := by
    intro hS
    have hB : B = [] := List.eq_nil_of_length_eq_zero (by rw [← hinv.len_sb, hS]; rfl)
    have h₁ := hinv.ch_oi₁
    have h₂ := hinv.ch_oi₂
    rw [hS, List.nil_append, hoi₁] at h₁
    rw [hB, List.nil_append, hoi₂] at h₂
    by_cases hlen : (chans₀ d₁).length ≤ (chans₀ d₂).length
    · have : X₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len_x₂]; omega)
      rw [this, passed_nil_right] at h₂
      exact List.cons_ne_nil _ _ h₂
    · have : X₁ = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len_x₁]; omega)
      rw [this, passed_nil_right] at h₁
      exact List.cons_ne_nil _ _ h₁
  obtain ⟨s, S', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨b', B', rfl⟩ := List.exists_cons_of_ne_nil (show B ≠ [] from λ h => by
    have := hinv.len_sb; rw [h] at this; simp at this)
  have h₁ := hinv.ch_oi₁
  rw [hoi₁, List.cons_append, List.cons.injEq] at h₁
  obtain ⟨rfl, h₁⟩ := h₁
  have h₂ := hinv.ch_oi₂
  rw [hoi₂, List.cons_append, List.cons.injEq] at h₂
  obtain ⟨rfl, h₂⟩ := h₂
  have e₁ : chans₀' d₁ ++ ChanMap.pushed [out] [v₁] d₁ = chans₀ d₁ := by
    simp [hsame d₁ (by simp [hD]) (by simp [hD]), hD]
  have e₂ : chans₀' d₂ ++ ChanMap.pushed [out] [v₁] d₂ = chans₀ d₂ := by
    simp [hsame d₂ (by simp [hD]) (by simp [hD]), hD]
  refine ⟨S', B', ?_, ?_, hinv.len_p₁, hinv.len_p₂, ?_, ?_, ?_, ?_, ?_, ?_,
    hinv.ch_oi₁', hinv.ch_oi₂', ?_⟩
  · simp only [e₁, e₂]; exact hinv.len_x₁
  · simp only [e₁, e₂]; exact hinv.len_x₂
  · have := hinv.len_sb; simp at this; exact this
  · simp only [e₁]; exact hinv.ch_d₁
  · simp only [e₂]; exact hinv.ch_d₂
  · simp only [e₁, e₂]; exact hinv.d_eq
  · simp [h₁, hD]
  · simp [h₂, hD]
  · intro y hy₁ hy₂ hy₃ hy₄
    rw [hinv.other y hy₁ hy₂ hy₃ hy₄, hsame y hy₃ hy₄]
    by_cases hy : y = out
    · subst hy; simp
    · simp [hy, Ne.symm hy]

private theorem inv_step_steer₁ {chans₀ chans₀' chans₁ : ChanMap χ V} {dv xv : V} {b : Bool}
  (hD : Distinct d₁ d₂ in₁ in₂ oi₁ oi₂ out)
  (hinv : Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out chans₀ chans₁ X₁ X₂ P₁ P₂ S B)
  (hb : InterpConsts.toBool dv = some b)
  (hpop : ∀ y, chans₀ y = ChanMap.pushed [d₁, in₁] [dv, xv] y ++ chans₀' y) :
    ∃ chans₁', LocalTauStar (newAtoms (Op := Op) flavor d₁ d₂ in₁ in₂ oi₁ out) chans₁
        (newAtoms flavor d₁ d₂ in₁ in₂ oi₁ out) chans₁' ∧
      ∃ X₁' X₂' P₁' P₂' S' B', Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out
        (λ y => chans₀' y ++ ChanMap.pushed (if b = flavor then [oi₁] else [])
          (if b = flavor then [xv] else []) y) chans₁' X₁' X₂' P₁' P₂' S' B' := by
  unfold Distinct at hD
  have hd₁ : chans₀ d₁ = dv :: chans₀' d₁ := by simp [hpop d₁, hD]
  have hin₁ : chans₀ in₁ = xv :: chans₀' in₁ := by simp [hpop in₁, hD]
  have hsame : ∀ y, y ≠ d₁ → y ≠ in₁ → chans₀' y = chans₀ y := λ y h₁ h₂ => by
    simp [hpop y, Ne.symm h₁, Ne.symm h₂]
  have hpush : ∀ y, ChanMap.pushed (if b = flavor then [oi₁] else [])
      (if b = flavor then [xv] else []) y = if y = oi₁ ∧ b = flavor then [xv] else [] :=
    λ y => pushed_ite
  -- The original channels after the step
  have e_d₁ : chans₀' d₁ ++ ChanMap.pushed (if b = flavor then [oi₁] else [])
      (if b = flavor then [xv] else []) d₁ = chans₀' d₁ := by simp [hpush, hD]
  have e_d₂ : chans₀' d₂ ++ ChanMap.pushed (if b = flavor then [oi₁] else [])
      (if b = flavor then [xv] else []) d₂ = chans₀ d₂ := by
    simp [hpush, hD, hsame d₂ (by simp [hD]) (by simp [hD])]
  have e_oi₁ : chans₀' oi₁ ++ ChanMap.pushed (if b = flavor then [oi₁] else [])
      (if b = flavor then [xv] else []) oi₁ = chans₀ oi₁ ++ (if b = flavor then [xv] else []) := by
    simp [hpush, hsame oi₁ (by simp [hD]) (by simp [hD])]
  have e_oi₂ : chans₀' oi₂ ++ ChanMap.pushed (if b = flavor then [oi₁] else [])
      (if b = flavor then [xv] else []) oi₂ = chans₀ oi₂ := by
    simp [hpush, hD, hsame oi₂ (by simp [hD]) (by simp [hD])]
  have e_y : ∀ y, y ≠ oi₁ → chans₀' y ++ ChanMap.pushed (if b = flavor then [oi₁] else [])
      (if b = flavor then [xv] else []) y = chans₀' y := λ y hy => by simp [hpush, hy]
  have hlen₁ : (chans₀ d₁).length = (chans₀' d₁).length + 1 := by rw [hd₁]; rfl
  by_cases hlen : (chans₀ d₁).length ≤ (chans₀ d₂).length
  · -- `steer₁` is not behind: nothing to do on the rewritten side
    have hX₂ : X₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len_x₂]; omega)
    refine ⟨chans₁, .refl, X₁ ++ [xv], X₂, P₁ ++ [dv], P₂, S, B, ?_, ?_, ?_, hinv.len_p₂,
      hinv.len_sb, ?_, ?_, ?_, ?_, ?_, hinv.ch_oi₁', hinv.ch_oi₂', ?_⟩
    · simp only [e_d₁, e_d₂, List.length_append, List.length_singleton]
      have := hinv.len_x₁; omega
    · simp only [e_d₁, e_d₂, hX₂, List.length_nil]; omega
    · simp [hinv.len_p₁]
    · simp only [e_d₁, hinv.ch_d₁, hd₁, List.append_assoc, List.singleton_append]
    · simp only [e_d₂, hinv.ch_d₂]
    · simp only [e_d₁, e_d₂, List.append_assoc, List.singleton_append, ← hd₁]
      exact hinv.d_eq
    · simp only [e_oi₁]
      rw [hinv.ch_oi₁, passed_append_single (by rw [hinv.len_p₁]), passed_single hb,
        List.append_assoc]
    · simp only [e_oi₂]; exact hinv.ch_oi₂
    · intro y hy₁ hy₂ hy₃ hy₄
      simp only [e_y y hy₃]
      rw [hinv.other y hy₁ hy₂ hy₃ hy₄]
      by_cases hy : y = in₁
      · subst hy; simp [hin₁, hD]
      · rw [hsame y hy₁ hy]; simp [hy]
  · -- `steer₁` is behind: the rewritten atoms process this position
    have hX₁ : X₁ = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len_x₁]; omega)
    have hP₁ : P₁ = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len_p₁, hX₁]; rfl)
    have hlx₂ := hinv.len_x₂
    have hlp₂ := hinv.len_p₂
    obtain ⟨x₂, X₂', rfl⟩ := List.exists_cons_of_length_pos
      (show 0 < X₂.length by rw [hlx₂]; omega)
    obtain ⟨p, P₂', rfl⟩ := List.exists_cons_of_length_pos
      (show 0 < P₂.length by rw [hlp₂]; simp)
    have hdeq := hinv.d_eq
    rw [hP₁, List.nil_append, hd₁, List.cons_append, List.cons.injEq] at hdeq
    obtain ⟨rfl, hdeq⟩ := hdeq
    have hin₁' : chans₁ in₁ = xv :: (chans₀' in₁ ++ (if in₁ = out then S else [])) := by
      rw [hinv.other in₁ (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD]), hin₁, hX₁]
      simp [hD]
    have hin₂' : chans₁ in₂ = x₂ :: (X₂' ++ chans₀ in₂ ++ (if in₂ = out then S else [])) := by
      rw [hinv.other in₂ (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD])]
      simp [hD]
    have hd₁' : chans₁ d₁ = dv :: chans₀' d₁ := by rw [hinv.ch_d₁, hP₁, hd₁]; rfl
    have hd₂' : chans₁ d₂ = dv :: (P₂' ++ chans₀ d₂) := by rw [hinv.ch_d₂]; rfl
    have hstep := fire_three (Op := Op) (flavor := flavor) (out := out)
      (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD])
      (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD])
      hin₁' hin₂' hd₁' hd₂' hinv.ch_oi₁' hb
    refine ⟨_, hstep, [], X₂', [], P₂', S ++ (if b = flavor then [xv] else []),
      B ++ (if b = flavor then [x₂] else []), ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [e_d₁, e_d₂, List.length_nil]; omega
    · simp only [e_d₁, e_d₂]
      simp only [List.length_cons] at hlx₂; omega
    · simpa using hlp₂
    · by_cases hbf : b = flavor <;> simp [hbf, hinv.len_sb]
    · simp [e_d₁, hD]
    · simp [e_d₂, hD]
    · simp only [e_d₁, e_d₂, List.nil_append]; exact hdeq
    · simp only [e_oi₁, hinv.ch_oi₁, hP₁, hX₁, passed_nil_left, List.append_nil]
    · simp only [e_oi₂, hinv.ch_oi₂, passed_cons, passed_single hb, List.append_assoc]
    · simp [hD, hinv.ch_oi₁']
    · simp [hD, hinv.ch_oi₂']
    · intro y hy₁ hy₂ hy₃ hy₄
      simp only [e_y y hy₃]
      by_cases hy₅ : y = in₁
      · subst hy₅
        by_cases ho : y = out
        · subst ho; simp [hD]
        · simp [hD, ho]
      · by_cases hy₆ : y = in₂
        · subst hy₆
          rw [hsame y hy₁ hy₅]
          by_cases ho : y = out
          · subst ho; simp [hD]
          · simp [hD, ho]
        · simp only [hy₅, hy₆, hy₁, hy₂, if_false]
          rw [hinv.other y hy₁ hy₂ hy₃ hy₄, hsame y hy₁ hy₅]
          by_cases ho : y = out
          · subst ho; simp [hy₅, hy₆]
          · simp [hy₅, hy₆, ho]

private theorem inv_step_steer₂ {chans₀ chans₀' chans₁ : ChanMap χ V} {dv xv : V} {b : Bool}
  (hD : Distinct d₁ d₂ in₁ in₂ oi₁ oi₂ out)
  (hinv : Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out chans₀ chans₁ X₁ X₂ P₁ P₂ S B)
  (hb : InterpConsts.toBool dv = some b)
  (hpop : ∀ y, chans₀ y = ChanMap.pushed [d₂, in₂] [dv, xv] y ++ chans₀' y) :
    ∃ chans₁', LocalTauStar (newAtoms (Op := Op) flavor d₁ d₂ in₁ in₂ oi₁ out) chans₁
        (newAtoms flavor d₁ d₂ in₁ in₂ oi₁ out) chans₁' ∧
      ∃ X₁' X₂' P₁' P₂' S' B', Inv flavor d₁ d₂ in₁ in₂ oi₁ oi₂ out
        (λ y => chans₀' y ++ ChanMap.pushed (if b = flavor then [oi₂] else [])
          (if b = flavor then [xv] else []) y) chans₁' X₁' X₂' P₁' P₂' S' B' := by
  unfold Distinct at hD
  have hd₂ : chans₀ d₂ = dv :: chans₀' d₂ := by simp [hpop d₂, hD]
  have hin₂ : chans₀ in₂ = xv :: chans₀' in₂ := by simp [hpop in₂, hD]
  have hsame : ∀ y, y ≠ d₂ → y ≠ in₂ → chans₀' y = chans₀ y := λ y h₁ h₂ => by
    simp [hpop y, Ne.symm h₁, Ne.symm h₂]
  have hpush : ∀ y, ChanMap.pushed (if b = flavor then [oi₂] else [])
      (if b = flavor then [xv] else []) y = if y = oi₂ ∧ b = flavor then [xv] else [] :=
    λ y => pushed_ite
  -- The original channels after the step
  have e_d₁ : chans₀' d₁ ++ ChanMap.pushed (if b = flavor then [oi₂] else [])
      (if b = flavor then [xv] else []) d₁ = chans₀ d₁ := by
    simp [hpush, hD, hsame d₁ (by simp [hD]) (by simp [hD])]
  have e_d₂ : chans₀' d₂ ++ ChanMap.pushed (if b = flavor then [oi₂] else [])
      (if b = flavor then [xv] else []) d₂ = chans₀' d₂ := by simp [hpush, hD]
  have e_oi₁ : chans₀' oi₁ ++ ChanMap.pushed (if b = flavor then [oi₂] else [])
      (if b = flavor then [xv] else []) oi₁ = chans₀ oi₁ := by
    simp [hpush, hD, hsame oi₁ (by simp [hD]) (by simp [hD])]
  have e_oi₂ : chans₀' oi₂ ++ ChanMap.pushed (if b = flavor then [oi₂] else [])
      (if b = flavor then [xv] else []) oi₂ = chans₀ oi₂ ++ (if b = flavor then [xv] else []) := by
    simp [hpush, hsame oi₂ (by simp [hD]) (by simp [hD])]
  have e_y : ∀ y, y ≠ oi₂ → chans₀' y ++ ChanMap.pushed (if b = flavor then [oi₂] else [])
      (if b = flavor then [xv] else []) y = chans₀' y := λ y hy => by simp [hpush, hy]
  have hlen₂ : (chans₀ d₂).length = (chans₀' d₂).length + 1 := by rw [hd₂]; rfl
  by_cases hlen : (chans₀ d₂).length ≤ (chans₀ d₁).length
  · -- `steer₂` is not behind: nothing to do on the rewritten side
    have hX₁ : X₁ = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len_x₁]; omega)
    refine ⟨chans₁, .refl, X₁, X₂ ++ [xv], P₁, P₂ ++ [dv], S, B, ?_, ?_, hinv.len_p₁, ?_,
      hinv.len_sb, ?_, ?_, ?_, ?_, ?_, hinv.ch_oi₁', hinv.ch_oi₂', ?_⟩
    · simp only [e_d₁, e_d₂, hX₁, List.length_nil]; omega
    · simp only [e_d₁, e_d₂, List.length_append, List.length_singleton]
      have := hinv.len_x₂; omega
    · simp [hinv.len_p₂]
    · simp only [e_d₁, hinv.ch_d₁]
    · simp only [e_d₂, hinv.ch_d₂, hd₂, List.append_assoc, List.singleton_append]
    · simp only [e_d₁, e_d₂, List.append_assoc, List.singleton_append, ← hd₂]
      exact hinv.d_eq
    · simp only [e_oi₁]; exact hinv.ch_oi₁
    · simp only [e_oi₂]
      rw [hinv.ch_oi₂, passed_append_single (by rw [hinv.len_p₂]), passed_single hb,
        List.append_assoc]
    · intro y hy₁ hy₂ hy₃ hy₄
      simp only [e_y y hy₄]
      rw [hinv.other y hy₁ hy₂ hy₃ hy₄]
      by_cases hy : y = in₂
      · subst hy; simp [hin₂, hD]
      · rw [hsame y hy₂ hy]; simp [hy]
  · -- `steer₂` is behind: the rewritten atoms process this position
    have hX₂ : X₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len_x₂]; omega)
    have hP₂ : P₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len_p₂, hX₂]; rfl)
    have hlx₁ := hinv.len_x₁
    have hlp₁ := hinv.len_p₁
    obtain ⟨x₁, X₁', rfl⟩ := List.exists_cons_of_length_pos
      (show 0 < X₁.length by rw [hlx₁]; omega)
    obtain ⟨p, P₁', rfl⟩ := List.exists_cons_of_length_pos
      (show 0 < P₁.length by rw [hlp₁]; simp)
    have hdeq := hinv.d_eq
    rw [hP₂, List.nil_append, hd₂, List.cons_append, List.cons.injEq] at hdeq
    obtain ⟨rfl, hdeq⟩ := hdeq
    have hin₁' : chans₁ in₁ = x₁ :: (X₁' ++ chans₀ in₁ ++ (if in₁ = out then S else [])) := by
      rw [hinv.other in₁ (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD])]
      simp [hD]
    have hin₂' : chans₁ in₂ = xv :: (chans₀' in₂ ++ (if in₂ = out then S else [])) := by
      rw [hinv.other in₂ (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD]), hin₂, hX₂]
      simp [hD]
    have hd₁' : chans₁ d₁ = p :: (P₁' ++ chans₀ d₁) := by rw [hinv.ch_d₁]; rfl
    have hd₂' : chans₁ d₂ = p :: chans₀' d₂ := by rw [hinv.ch_d₂, hP₂, hd₂]; rfl
    have hstep := fire_three (Op := Op) (flavor := flavor) (out := out)
      (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD])
      (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD]) (by simp [hD])
      hin₁' hin₂' hd₁' hd₂' hinv.ch_oi₁' hb
    refine ⟨_, hstep, X₁', [], P₁', [], S ++ (if b = flavor then [x₁] else []),
      B ++ (if b = flavor then [xv] else []), ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [e_d₁, e_d₂]
      simp only [List.length_cons] at hlx₁; omega
    · simp only [e_d₁, e_d₂, List.length_nil]; omega
    · simpa using hlp₁
    · by_cases hbf : b = flavor <;> simp [hbf, hinv.len_sb]
    · simp [e_d₁, hD]
    · simp [e_d₂, hD]
    · simp only [e_d₁, e_d₂, List.nil_append]; exact hdeq
    · simp only [e_oi₁, hinv.ch_oi₁, passed_cons, passed_single hb, List.append_assoc]
    · simp only [e_oi₂, hinv.ch_oi₂, hP₂, hX₂, passed_nil_left, List.append_nil]
    · simp [hD, hinv.ch_oi₁']
    · simp [hD, hinv.ch_oi₂']
    · intro y hy₁ hy₂ hy₃ hy₄
      simp only [e_y y hy₄]
      by_cases hy₅ : y = in₁
      · subst hy₅
        rw [hsame y hy₂ (by simp [hD])]
        by_cases ho : y = out
        · subst ho; simp [hD]
        · simp [hD, ho]
      · by_cases hy₆ : y = in₂
        · subst hy₆
          by_cases ho : y = out
          · subst ho; simp [hD]
          · simp [hD, ho]
        · simp only [hy₅, hy₆, hy₁, hy₂, if_false]
          rw [hinv.other y hy₁ hy₂ hy₃ hy₄, hsame y hy₂ hy₆]
          by_cases ho : y = out
          · subst ho; simp [hy₅, hy₆]
          · simp [hy₅, hy₆, ho]

end Inv

end OrderSteerSteer

theorem order_steer_steer_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ i₃ : Nat}
  {flavor : Bool} {orderInput₁ orderInput₂ output decider₁ input₁ decider₂ input₂ : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.order 2) [orderInput₁, orderInput₂] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.steer flavor 1) [decider₁, input₁] [orderInput₁]))
  (h₃ : proc.atoms[i₃]? = some (.async (.steer flavor 1) [decider₂, input₂] [orderInput₂]))
  (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
  (hfork : SameFork proc.atoms decider₁ decider₂) :
    RuleOK proc [i₃, i₂, i₁] [
      .order #v[input₁, input₂] orderInput₁,
      .steer flavor decider₁ #v[orderInput₁] #v[output],
      .sink #v[decider₂],
    ]
  := by
  open OrderSteerSteer in
  have hP : matchedOf proc.atoms [i₃, i₂, i₁] = [
      .async (.steer flavor 1) [decider₂, input₂] [orderInput₂],
      .async (.steer flavor 1) [decider₁, input₁] [orderInput₁],
      .async (.order 2) [orderInput₁, orderInput₂] [output]] := by
    simp [h₁, h₂, h₃]
  have hP' : ([.order #v[input₁, input₂] orderInput₁, .steer flavor decider₁ #v[orderInput₁] #v[output],
      .sink #v[decider₂]] : AtomicProcs Op χ V) =
      [.async (.order 2) [input₁, input₂] [orderInput₁],
        .async (.steer flavor 1) [decider₁, orderInput₁] [output],
        .async (.sink 1) [decider₂] []] := by
    simp [AtomicProc.order, AtomicProc.steer, AtomicProc.sink]
  -- Facts from affineness
  have hdj₂₁ := haff.atom_disjoint h₂ h₁ hne₂₁
  have hdj₃₁ := haff.atom_disjoint h₃ h₁ hne₃₁
  have hdj₃₂ := haff.atom_disjoint h₃ h₂ hne₃₂
  -- `output` is not written by the fork behind the deciders
  obtain ⟨k, insF, outsF, hF, hd₁F, hd₂F⟩ := hfork
  obtain ⟨j, hj, hgetF⟩ := List.getElem_of_mem hF
  have hj₁ : j ≠ i₁ := by
    rintro rfl
    rw [List.getElem?_eq_getElem hj, hgetF] at h₁
    simp at h₁
  have hdjF := (haff.atom_disjoint (List.getElem?_eq_some_iff.mpr ⟨hj, hgetF⟩) h₁ hj₁).2
  have hD : Distinct decider₁ decider₂ input₁ input₂ orderInput₁ orderInput₂ output :=
    distinct_of
      (ne_of_disjoint hdj₃₂.1 (by simp) (by simp)).symm
      (by simpa using (haff.atom_nodup h₂).1)
      (ne_of_disjoint hdj₃₂.1 (by simp) (by simp)).symm
      (ne_of_disjoint hdj₂₁.1 (by simp) (by simp))
      (ne_of_disjoint hdj₂₁.1 (by simp) (by simp))
      (ne_of_disjoint hdj₃₂.1 (by simp) (by simp))
      (by simpa using (haff.atom_nodup h₃).1)
      (ne_of_disjoint hdj₃₁.1 (by simp) (by simp))
      (ne_of_disjoint hdj₃₁.1 (by simp) (by simp))
      (ne_of_disjoint hdj₃₂.1 (by simp) (by simp)).symm
      (ne_of_disjoint hdj₂₁.1 (by simp) (by simp))
      (ne_of_disjoint hdj₂₁.1 (by simp) (by simp))
      (ne_of_disjoint hdj₃₁.1 (by simp) (by simp))
      (ne_of_disjoint hdj₃₁.1 (by simp) (by simp))
      (by simpa using (haff.atom_nodup h₁).1)
      (ne_of_disjoint hdjF hd₁F (by simp)).symm
      (ne_of_disjoint hdjF hd₂F (by simp)).symm
      (ne_of_disjoint hdj₂₁.2 (by simp) (by simp)).symm
      (ne_of_disjoint hdj₃₁.2 (by simp) (by simp)).symm
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₃, i₂, i₁] ∧
    L₁ = newAtoms flavor decider₁ decider₂ input₁ input₂ orderInput₁ output ∧
    ∃ X₁ X₂ P₁ P₂ S B, Inv flavor decider₁ decider₂ input₁ input₂ orderInput₁ orderInput₂ output
      chans₀ chans₁ X₁ X₂ P₁ P₂ S B, ?_, ?_⟩
  · have hD' := hD
    unfold Distinct at hD'
    constructor
    · simp [hne₂₁, hne₃₁, hne₃₂]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1,
        (List.getElem?_eq_some_iff.mp h₃).1]
    · simp [hP', hD']
    · simp [hP', hD']
    · simp [hP', hP]
    · simp [hP', hP]
  · constructor
    · exact ⟨rfl, rfl, [], [], [], [], [], [], inv_init⟩
    · rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, rfl, X₁, X₂, P₁, P₂, S, B, hinv⟩ hpop
      -- `x` is read by the context, so it is none of the matched inputs
      obtain ⟨chans₁', hpop', hinv'⟩ := inv_frame_pop hinv
        (by rintro rfl; simp [hP] at hx) (by rintro rfl; simp [hP] at hx)
        (by rintro rfl; simp [hP] at hx) (by rintro rfl; simp [hP] at hx)
        (by rintro rfl; simp [hP] at hx) (by rintro rfl; simp [hP] at hx) hpop
      exact ⟨chans₁', hpop', rfl, rfl, X₁, X₂, P₁, P₂, S, B, hinv'⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals hlen hx hnd hfp ⟨rfl, rfl, X₁, X₂, P₁, P₂, S, B, hinv⟩
      have ho₁ : orderInput₁ ∉ outs := λ h => by simpa [hP] using (hx _ h).1
      have ho₂ : orderInput₂ ∉ outs := λ h => by simpa [hP] using (hx _ h).1
      have hout : output ∉ outs := λ h => by simpa [hP] using (hx _ h).1
      -- Both deciders receive the same pushes from the fork
      have hd : ChanMap.pushed outs vals decider₁ = ChanMap.pushed outs vals decider₂ := by
        by_cases hm : decider₁ ∈ outs ∨ decider₂ ∈ outs
        · obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ outs, x ∈ outsF := by
            rcases hm with hm | hm
            exacts [⟨_, hm, hd₁F⟩, ⟨_, hm, hd₂F⟩]
          obtain ⟨rfl, w, -, hw⟩ := hfp x hx₁ k insF outsF hF hx₂
          rw [pushed_of_forall_eq hnd hlen hw hd₁F, pushed_of_forall_eq hnd hlen hw hd₂F]
        · simp only [not_or] at hm
          rw [ChanMap.pushed_not_mem hm.1, ChanMap.pushed_not_mem hm.2]
      exact ⟨rfl, rfl, X₁, X₂, P₁, P₂, S, B, inv_frame_push hinv hd ho₁ ho₂ hout⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _ ⟨rfl, rfl, X₁, X₂, P₁, P₂, S, B, hinv⟩
        hget hinterp hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        -- `steer₂` fires
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, dv, xv, b, rfl, hb, rfl, rfl⟩ := hinterp.steer_inv hlen₁
        obtain ⟨chans₁', hstep, X₁', X₂', P₁', P₂', S', B', hinv'⟩ :=
          inv_step_steer₂ (Op := Op) hD hinv hb hpop
        exact ⟨_, chans₁', hstep, by simp, rfl, X₁', X₂', P₁', P₂', S', B', hinv'⟩
      | 1, hget =>
        -- `steer₁` fires
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, dv, xv, b, rfl, hb, rfl, rfl⟩ := hinterp.steer_inv hlen₁
        obtain ⟨chans₁', hstep, X₁', X₂', P₁', P₂', S', B', hinv'⟩ :=
          inv_step_steer₁ (Op := Op) hD hinv hb hpop
        exact ⟨_, chans₁', hstep, by simp, rfl, X₁', X₂', P₁', P₂', S', B', hinv'⟩
      | 2, hget =>
        -- The order fires: the rewritten graph has already output the value
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, v₁, rest, rfl, rfl⟩ := hinterp.order_inv
        obtain ⟨v₂, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hlen₁.symm)
        obtain ⟨S', B', hinv'⟩ := inv_step_order hD hinv hpop
        exact ⟨_, _, .refl, by simp, rfl, X₁, X₂, P₁, P₂, S', B', hinv'⟩
      | n + 3, hget => simp at hget
  · rintro L₁ chans₁ ⟨_, rfl, X₁, X₂, P₁, P₂, S, B, hinv⟩
    exact ⟨rfl, inv_empty hinv⟩

end Wavelet.Compile.DeadCodeElim
