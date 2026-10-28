import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! `sync-order-order`: two orders feeding the same operator can be combined. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

namespace SyncOrderOrder

/-! List lemmas. -/

private theorem vector_toList_replace [DecidableEq α] {xs : Vector α n} {a b : α} :
    (xs.replace a b).toList = xs.toList.replace a b := by
  rcases xs with ⟨⟨l⟩, h⟩
  simp [Vector.replace, Vector.toList]

@[simp]
private theorem toList_toVector' {xs : List α} : xs.toVector.toList = xs := rfl

private theorem take_succ_of_drop_eq_cons {l W : List V} {n : Nat} {w : V}
  (h : l.drop n = w :: W) : l.take (n + 1) = l.take n ++ [w] := by
  induction n generalizing l with
  | zero => subst h; simp
  | succ n ih =>
    cases l with
    | nil => simp at h
    | cons x l =>
      simp only [List.drop_succ_cons] at h
      simp [List.take_succ_cons, ih h]

private theorem drop_succ_of_drop_eq_cons {l W : List V} {n : Nat} {w : V}
  (h : l.drop n = w :: W) : l.drop (n + 1) = W := by
  rw [← List.drop_drop, h]; rfl

/-- Heads of the given (non-empty) channels. -/
private def heads (chans : ChanMap χ V) (names : List χ) : List V :=
  names.flatMap (λ c => (chans c).take 1)

private theorem length_heads {chans : ChanMap χ V} {names : List χ}
  (hne : ∀ c ∈ names, chans c ≠ []) : (heads chans names).length = names.length := by
  induction names with
  | nil => rfl
  | cons c names ih =>
    obtain ⟨w, W, hw⟩ := List.exists_cons_of_ne_nil (hne c (by simp))
    simp only [heads, List.flatMap_cons, List.length_append, hw, List.take_succ_cons,
      List.take_zero, List.length_cons, List.length_nil] at ih ⊢
    rw [ih (λ c' hc' => hne c' (by simp [hc']))]
    omega

/-! The invariant. -/

/-- Distinctness of the channel names (in both directions, for `simp`). -/
private def Distinct (o₁ o₂ a₁ c₂ : χ) (t₂ r₁ : List χ) : Prop :=
  (o₁ ≠ o₂ ∧ o₁ ≠ a₁ ∧ o₁ ≠ c₂ ∧ o₂ ≠ a₁ ∧ o₂ ≠ c₂ ∧ a₁ ≠ c₂) ∧
  (o₂ ≠ o₁ ∧ a₁ ≠ o₁ ∧ c₂ ≠ o₁ ∧ a₁ ≠ o₂ ∧ c₂ ≠ o₂ ∧ c₂ ≠ a₁) ∧
  (o₁ ∉ t₂ ∧ o₁ ∉ r₁ ∧ o₂ ∉ t₂ ∧ o₂ ∉ r₁ ∧ a₁ ∉ t₂ ∧ a₁ ∉ r₁ ∧ c₂ ∉ t₂ ∧ c₂ ∉ r₁) ∧
  (∀ y ∈ t₂, y ∉ r₁) ∧ t₂.Nodup ∧ r₁.Nodup

private theorem distinct_of {o₁ o₂ a₁ c₂ : χ} {t₂ r₁ : List χ}
  (h₁ : o₁ ≠ o₂) (h₂ : o₁ ≠ a₁) (h₃ : o₁ ≠ c₂) (h₄ : o₂ ≠ a₁) (h₅ : o₂ ≠ c₂) (h₆ : a₁ ≠ c₂)
  (h₇ : o₁ ∉ t₂) (h₈ : o₁ ∉ r₁) (h₉ : o₂ ∉ t₂) (h₁₀ : o₂ ∉ r₁) (h₁₁ : a₁ ∉ t₂) (h₁₂ : a₁ ∉ r₁)
  (h₁₃ : c₂ ∉ t₂) (h₁₄ : c₂ ∉ r₁) (h₁₅ : ∀ y ∈ t₂, y ∉ r₁) (h₁₆ : t₂.Nodup) (h₁₇ : r₁.Nodup) :
    Distinct o₁ o₂ a₁ c₂ t₂ r₁ :=
  ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, ⟨h₁.symm, h₂.symm, h₃.symm, h₄.symm, h₅.symm, h₆.symm⟩,
    ⟨h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩, h₁₅, h₁₆, h₁₇⟩

/--
The simulation invariant. With `a`/`b` the numbers of values in `o₁`/`o₂`, the merged
order (with inputs `c₂ :: t₂ ++ r₁`) has fired `min a b` times more than the original op.
- The rewritten op reads `a₁` directly, so `a₁` also holds the values of `o₁`.
- `o₂` holds the first `min a b` values of `o₂`; the others are still in `c₂`.
- `X y` is the extra prefix of the other inputs of the merged order
  (of length `b - min a b` for `t₂` and `a - min a b` for `r₁`).
-/
private structure Inv (o₁ o₂ a₁ c₂ : χ) (t₂ r₁ : List χ)
    (chans₀ chans₁ : ChanMap χ V) (X : χ → List V) : Prop where
  x_nil : ∀ y, y ∉ t₂ → y ∉ r₁ → X y = []
  x_t₂ : ∀ y ∈ t₂, (X y).length =
    (chans₀ o₂).length - min (chans₀ o₁).length (chans₀ o₂).length
  x_r₁ : ∀ y ∈ r₁, (X y).length =
    (chans₀ o₁).length - min (chans₀ o₁).length (chans₀ o₂).length
  ch_o₁ : chans₁ o₁ = []
  ch_o₂ : chans₁ o₂ = (chans₀ o₂).take (min (chans₀ o₁).length (chans₀ o₂).length)
  ch_a₁ : chans₁ a₁ = chans₀ o₁ ++ chans₀ a₁
  ch_c₂ : chans₁ c₂ = (chans₀ o₂).drop (min (chans₀ o₁).length (chans₀ o₂).length) ++ chans₀ c₂
  other : ∀ y, y ≠ o₁ → y ≠ o₂ → y ≠ a₁ → y ≠ c₂ → chans₁ y = X y ++ chans₀ y

section Inv

variable {o₁ o₂ a₁ c₂ : χ} {t₂ r₁ : List χ}

private theorem inv_init :
    Inv o₁ o₂ a₁ c₂ t₂ r₁ (.empty : ChanMap χ V) .empty (λ _ => []) := by
  refine ⟨λ _ _ _ => rfl, λ _ _ => by simp, λ _ _ => by simp, rfl, by simp, by simp,
    by simp, λ _ _ _ _ _ => by simp⟩

private theorem inv_empty {chans₁ : ChanMap χ V} {X : χ → List V}
  (hinv : Inv o₁ o₂ a₁ c₂ t₂ r₁ .empty chans₁ X) : chans₁ = .empty := by
  have hX : ∀ y, X y = [] := by
    intro y
    by_cases h₁ : y ∈ t₂
    · exact List.eq_nil_of_length_eq_zero (by simpa using hinv.x_t₂ y h₁)
    · by_cases c₂ : y ∈ r₁
      · exact List.eq_nil_of_length_eq_zero (by simpa using hinv.x_r₁ y c₂)
      · exact hinv.x_nil y h₁ c₂
  funext y
  by_cases hy₁ : y = o₁
  · subst hy₁; simp [hinv.ch_o₁]
  · by_cases hy₂ : y = o₂
    · subst hy₂; simp [hinv.ch_o₂]
    · by_cases hy₃ : y = a₁
      · subst hy₃; simp [hinv.ch_a₁]
      · by_cases hy₄ : y = c₂
        · subst hy₄; simp [hinv.ch_c₂]
        · simp [hinv.other y hy₁ hy₂ hy₃ hy₄, hX]

end Inv

variable [DecidableEq χ]

/-! Channel updates. -/

private theorem mem_of_mem_replace {l : List χ} {a b y : χ}
  (h : y ∈ l.replace a b) : y ∈ l ∨ y = b := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [List.replace_cons] at h
    by_cases hax : (a == x) = true
    · simp only [hax] at h
      rcases List.mem_cons.mp h with h | h
      · exact .inr h
      · exact .inl (List.mem_cons_of_mem _ h)
    · simp only [Bool.not_eq_true] at hax
      simp only [hax] at h
      rcases List.mem_cons.mp h with h | h
      · exact .inl (h ▸ List.mem_cons_self ..)
      · rcases ih h with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h

private theorem nodup_replace {l : List χ} {a b : χ}
  (hnd : l.Nodup) (hb : b ∉ l) : (l.replace a b).Nodup := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    have ⟨hbx, hb'⟩ : b ≠ x ∧ b ∉ l := by simpa using hb
    rw [List.replace_cons]
    by_cases hax : (a == x) = true
    · simp only [hax]
      exact List.nodup_cons.mpr ⟨hb', hnd'⟩
    · simp only [Bool.not_eq_true] at hax
      simp only [hax]
      refine List.nodup_cons.mpr ⟨λ h => ?_, ih hnd' hb'⟩
      rcases mem_of_mem_replace h with h | h
      · exact hx h
      · exact hbx h.symm

private theorem pushed_replace {l : List χ} {vals : List V} {a b y : χ}
  (hnd : l.Nodup) (hb : b ∉ l) :
    ChanMap.pushed (l.replace a b) vals y =
      if y = b then ChanMap.pushed l vals a else if y = a then [] else ChanMap.pushed l vals y := by
  induction l generalizing vals with
  | nil => by_cases h₁ : y = b <;> by_cases h₂ : y = a <;> simp [h₁, h₂]
  | cons x l ih =>
    cases vals with
    | nil => by_cases h₁ : y = b <;> by_cases h₂ : y = a <;> simp [h₁, h₂]
    | cons v vals =>
      have ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      have ⟨hbx, hb'⟩ : b ≠ x ∧ b ∉ l := by simpa using hb
      by_cases hxa : x = a
      · subst hxa
        rw [List.replace_cons_self]
        by_cases h₁ : y = b
        · subst h₁; simp [ChanMap.pushed_not_mem hx, ChanMap.pushed_not_mem hb']
        · by_cases h₂ : y = x
          · subst h₂; simp [Ne.symm h₁, h₁, ChanMap.pushed_not_mem hx]
          · simp [h₁, h₂, Ne.symm h₁, Ne.symm h₂]
      · have hax : (a == x) = false := by simpa using Ne.symm hxa
        simp only [List.replace_cons, hax, ChanMap.pushed_cons, ih hnd' hb']
        by_cases h₁ : y = b
        · subst h₁; simp [Ne.symm hbx, hxa]
        · by_cases h₂ : y = a
          · subst h₂; simp [hxa, h₁]
          · simp [h₁, h₂]

private theorem pushed_singleton {names : List χ} {vals : List V} {y : χ}
  (hnd : names.Nodup) (hlen : names.length = vals.length) (hy : y ∈ names) :
    ∃ v, ChanMap.pushed names vals y = [v] := by
  induction names generalizing vals with
  | nil => simp at hy
  | cons x names ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vals =>
      have ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      rw [ChanMap.pushed_cons]
      by_cases hxy : x = y
      · subst hxy
        exact ⟨v, by simp [ChanMap.pushed_not_mem hx]⟩
      · have hy' : y ∈ names := by
          rcases List.mem_cons.mp hy with h | h
          · exact absurd h.symm hxy
          · exact h
        obtain ⟨w, hw⟩ := ih hnd' (by simpa using hlen) hy'
        exact ⟨w, by simp [hxy, hw]⟩

private theorem pushed_heads {chans : ChanMap χ V} {names : List χ}
  (hnd : names.Nodup) (hne : ∀ c ∈ names, chans c ≠ []) (y : χ) :
    ChanMap.pushed names (heads chans names) y = if y ∈ names then (chans y).take 1 else [] := by
  induction names with
  | nil => simp [heads]
  | cons c names ih =>
    have ⟨hc, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨w, W, hw⟩ := List.exists_cons_of_ne_nil (hne c (by simp))
    have ih' := ih hnd' (λ c' hc' => hne c' (by simp [hc']))
    simp only [heads] at ih'
    simp only [heads, List.flatMap_cons, hw, List.take_succ_cons, List.take_zero,
      List.singleton_append, ChanMap.pushed_cons, ih']
    by_cases hcy : c = y
    · subst hcy; simp [hc, hw]
    · simp [hcy, Ne.symm hcy]

/-- The rewritten channels determined by the original channels and the extra prefixes. -/
private def canon (o₁ o₂ a₁ c₂ : χ) (chans₀ : ChanMap χ V) (X : χ → List V) : ChanMap χ V :=
  λ y =>
    if y = o₁ then []
    else if y = o₂ then (chans₀ o₂).take (min (chans₀ o₁).length (chans₀ o₂).length)
    else if y = a₁ then chans₀ o₁ ++ chans₀ a₁
    else if y = c₂ then (chans₀ o₂).drop (min (chans₀ o₁).length (chans₀ o₂).length) ++ chans₀ c₂
    else X y ++ chans₀ y

section Inv

variable {o₁ o₂ a₁ c₂ : χ} {t₂ r₁ : List χ}

private theorem inv_canon {chans₀ : ChanMap χ V} {X : χ → List V}
  (hD : Distinct o₁ o₂ a₁ c₂ t₂ r₁)
  (hx_nil : ∀ y, y ∉ t₂ → y ∉ r₁ → X y = [])
  (hx_t₂ : ∀ y ∈ t₂, (X y).length =
    (chans₀ o₂).length - min (chans₀ o₁).length (chans₀ o₂).length)
  (hx_r₁ : ∀ y ∈ r₁, (X y).length =
    (chans₀ o₁).length - min (chans₀ o₁).length (chans₀ o₂).length) :
    Inv o₁ o₂ a₁ c₂ t₂ r₁ chans₀ (canon o₁ o₂ a₁ c₂ chans₀ X) X := by
  unfold Distinct at hD
  refine ⟨hx_nil, hx_t₂, hx_r₁, ?_, ?_, ?_, ?_, ?_⟩
  · simp [canon]
  · simp [canon, hD]
  · simp [canon, hD]
  · simp [canon, hD]
  · intro y hy₁ hy₂ hy₃ hy₄
    simp [canon, hy₁, hy₂, hy₃, hy₄]

private theorem inv_frame_pop {chans₀ chans₀' chans₁ : ChanMap χ V} {X : χ → List V}
  {x : χ} {v : V}
  (hD : Distinct o₁ o₂ a₁ c₂ t₂ r₁)
  (hinv : Inv o₁ o₂ a₁ c₂ t₂ r₁ chans₀ chans₁ X)
  (hxo₁ : x ≠ o₁) (hxo₂ : x ≠ o₂) (hxa₁ : x ≠ a₁) (hxc₂ : x ≠ c₂) (hxt₂ : x ∉ t₂) (hxr₁ : x ∉ r₁)
  (hpop : ∀ y, chans₀ y = (if y = x then [v] else []) ++ chans₀' y) :
    ∃ chans₁', (∀ y, chans₁ y = (if y = x then [v] else []) ++ chans₁' y) ∧
      Inv o₁ o₂ a₁ c₂ t₂ r₁ chans₀' chans₁' X := by
  have hsame : ∀ y, y ≠ x → chans₀' y = chans₀ y := λ y hy => by simp [hpop y, hy]
  have e₁ := hsame o₁ (Ne.symm hxo₁)
  have e₂ := hsame o₂ (Ne.symm hxo₂)
  refine ⟨canon o₁ o₂ a₁ c₂ chans₀' X, ?_, ?_⟩
  · intro y
    by_cases hy₁ : y = o₁
    · subst hy₁; simp [canon, hinv.ch_o₁, Ne.symm hxo₁]
    · by_cases hy₂ : y = o₂
      · subst hy₂; simp [canon, hinv.ch_o₂, Ne.symm hxo₂, hy₁, e₁, e₂]
      · by_cases hy₃ : y = a₁
        · subst hy₃
          simp [canon, hinv.ch_a₁, Ne.symm hxa₁, hy₁, hy₂, e₁, hsame y (Ne.symm hxa₁)]
        · by_cases hy₄ : y = c₂
          · subst hy₄
            simp [canon, hinv.ch_c₂, Ne.symm hxc₂, hy₁, hy₂, hy₃, e₁, e₂, hsame y (Ne.symm hxc₂)]
          · simp only [canon, hy₁, hy₂, hy₃, hy₄, if_false, hinv.other y hy₁ hy₂ hy₃ hy₄, hpop y]
            by_cases hy : y = x
            · subst hy; simp [hinv.x_nil y hxt₂ hxr₁]
            · simp [hy]
  · refine inv_canon hD hinv.x_nil ?_ ?_
    · intro y hy; rw [e₁, e₂]; exact hinv.x_t₂ y hy
    · intro y hy; rw [e₁, e₂]; exact hinv.x_r₁ y hy

private theorem inv_frame_push {chans₀ chans₁ : ChanMap χ V} {X : χ → List V}
  {outs : List χ} {vals : List V}
  (hinv : Inv o₁ o₂ a₁ c₂ t₂ r₁ chans₀ chans₁ X)
  (ho₁ : o₁ ∉ outs) (ho₂ : o₂ ∉ outs) :
    Inv o₁ o₂ a₁ c₂ t₂ r₁
      (λ y => chans₀ y ++ ChanMap.pushed outs vals y)
      (λ y => chans₁ y ++ ChanMap.pushed outs vals y) X := by
  have p₁ := ChanMap.pushed_not_mem (vals := vals) ho₁
  have p₂ := ChanMap.pushed_not_mem (vals := vals) ho₂
  refine ⟨hinv.x_nil, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy; simp only [p₁, p₂, List.append_nil]; exact hinv.x_t₂ y hy
  · intro y hy; simp only [p₁, p₂, List.append_nil]; exact hinv.x_r₁ y hy
  · simp [p₁, hinv.ch_o₁]
  · simp [p₁, p₂, hinv.ch_o₂]
  · simp [p₁, hinv.ch_a₁]
  · simp [p₁, p₂, hinv.ch_c₂]
  · intro y hy₁ hy₂ hy₃ hy₄
    simp [hinv.other y hy₁ hy₂ hy₃ hy₄]

private theorem inv_step_op {chans₀ chans₀' chans₁ : ChanMap χ V} {X : χ → List V}
  {ins : List χ} {vals : List V}
  (hD : Distinct o₁ o₂ a₁ c₂ t₂ r₁)
  (hinv : Inv o₁ o₂ a₁ c₂ t₂ r₁ chans₀ chans₁ X)
  (hnd : ins.Nodup) (hlen : ins.length = vals.length)
  (ho₁ : o₁ ∈ ins) (ho₂ : o₂ ∈ ins) (ha₁ : a₁ ∉ ins) (hc₂ : c₂ ∉ ins)
  (ht₂ : ∀ y ∈ t₂, y ∉ ins) (hr₁ : ∀ y ∈ r₁, y ∉ ins)
  (hpop : ∀ y, chans₀ y = ChanMap.pushed ins vals y ++ chans₀' y) :
    (∀ y, chans₁ y =
      ChanMap.pushed (ins.replace o₁ a₁) vals y ++ canon o₁ o₂ a₁ c₂ chans₀' X y) ∧
      Inv o₁ o₂ a₁ c₂ t₂ r₁ chans₀' (canon o₁ o₂ a₁ c₂ chans₀' X) X := by
  have hD' := hD
  unfold Distinct at hD'
  obtain ⟨u₁, hu₁⟩ := pushed_singleton hnd hlen ho₁
  obtain ⟨u₂, hu₂⟩ := pushed_singleton hnd hlen ho₂
  have hc₁ : chans₀ o₁ = u₁ :: chans₀' o₁ := by rw [hpop o₁, hu₁]; rfl
  have hc₂' : chans₀ o₂ = u₂ :: chans₀' o₂ := by rw [hpop o₂, hu₂]; rfl
  have hl₁ : (chans₀ o₁).length = (chans₀' o₁).length + 1 := by rw [hc₁]; rfl
  have hl₂ : (chans₀ o₂).length = (chans₀' o₂).length + 1 := by rw [hc₂']; rfl
  have hsame : ∀ y, y ∉ ins → chans₀' y = chans₀ y := λ y hy => by
    rw [hpop y, ChanMap.pushed_not_mem hy]; rfl
  have hm : min (chans₀ o₁).length (chans₀ o₂).length =
      min (chans₀' o₁).length (chans₀' o₂).length + 1 := by omega
  constructor
  · intro y
    rw [pushed_replace hnd ha₁]
    by_cases hy₃ : y = a₁
    · subst hy₃
      rw [hinv.ch_a₁, hc₁, hu₁]
      simp [canon, hD', hsame y ha₁]
    · by_cases hy₁ : y = o₁
      · subst hy₁
        simp [canon, hinv.ch_o₁, hD']
      · by_cases hy₂ : y = o₂
        · subst hy₂
          rw [hinv.ch_o₂, hm, hc₂', hu₂]
          simp [canon, hD']
        · by_cases hy₄ : y = c₂
          · subst hy₄
            rw [hinv.ch_c₂, hm, hc₂', ChanMap.pushed_not_mem hc₂]
            simp [canon, hD', hsame y hc₂]
          · rw [hinv.other y hy₁ hy₂ hy₃ hy₄, hpop y]
            simp only [canon, hy₁, hy₂, hy₃, hy₄, if_false]
            by_cases hy : y ∈ ins
            · have hX : X y = [] := hinv.x_nil y (λ h => ht₂ y h hy) (λ h => hr₁ y h hy)
              simp [hX]
            · simp [ChanMap.pushed_not_mem hy]
  · refine inv_canon hD hinv.x_nil ?_ ?_
    · intro y hy; have := hinv.x_t₂ y hy; omega
    · intro y hy; have := hinv.x_r₁ y hy; omega

end Inv

variable [Arity Op] [InterpConsts V]

/-- An order fires on the heads of its (distinct, non-empty) inputs. -/
private theorem order_fire {L : AtomicProcs Op χ V} {chans : ChanMap χ V}
  {k : Nat} [NeZero k] {c₀ out : χ} {cs : List χ} {w : V} {W : List V}
  (hmem : .async (.order k) (c₀ :: cs) [out] ∈ L)
  (hk : (c₀ :: cs).length = k)
  (hnd : (c₀ :: cs).Nodup)
  (hc₀ : chans c₀ = w :: W)
  (hne : ∀ c ∈ cs, chans c ≠ []) :
    LocalTauStar L chans L (λ y => (if y ∈ c₀ :: cs then (chans y).tail else chans y) ++
      (if y = out then [w] else [])) := by
  have ⟨hc₀', hnd'⟩ := List.nodup_cons.mp hnd
  have hlen : (w :: heads chans cs).length = k := by
    rw [← hk]; simp [length_heads hne]
  have hstep := LocalTauStar.async_list_mem
    (L := L) (aop := .order k) (allInputs := c₀ :: cs) (allOutputs := [out])
    (inputs := c₀ :: cs) (inputVals := w :: heads chans cs) (outputs := [out]) (outputVals := [w])
    (chans := chans) (chans' := λ y => if y ∈ c₀ :: cs then (chans y).tail else chans y)
    hmem (.interp_order hk hlen) (by rw [hk, hlen]) rfl
    (by
      intro y
      rw [ChanMap.pushed_cons, pushed_heads hnd' hne]
      by_cases h₁ : c₀ = y
      · subst h₁; simp [hc₀', hc₀]
      · by_cases h₂ : y ∈ cs
        · obtain ⟨u, U, hu⟩ := List.exists_cons_of_ne_nil (hne y h₂)
          simp [h₁, h₂, hu]
        · simp [h₁, h₂, Ne.symm h₁])
  apply hstep.eq_rhs rfl
  funext y
  by_cases h : out = y
  · subst h; simp
  · simp [h, Ne.symm h]

section Inv

variable {o₁ o₂ a₁ c₂ : χ} {t₂ r₁ : List χ}

private theorem inv_step_order₁ {L : AtomicProcs Op χ V} {k : Nat} [NeZero k]
  {chans₀ chans₀' chans₁ : ChanMap χ V} {X : χ → List V} {v : V} {us : List V}
  (hD : Distinct o₁ o₂ a₁ c₂ t₂ r₁)
  (hmem : .async (.order k) (c₂ :: (t₂ ++ r₁)) [o₂] ∈ L)
  (hk : (c₂ :: (t₂ ++ r₁)).length = k)
  (hinv : Inv o₁ o₂ a₁ c₂ t₂ r₁ chans₀ chans₁ X)
  (hlen : r₁.length = us.length)
  (hpop : ∀ y, chans₀ y = ChanMap.pushed (a₁ :: r₁) (v :: us) y ++ chans₀' y) :
    ∃ chans₁' X', LocalTauStar L chans₁ L chans₁' ∧
      Inv o₁ o₂ a₁ c₂ t₂ r₁ (λ y => chans₀' y ++ ChanMap.pushed [o₁] [v] y) chans₁' X' := by
  have hD' := hD
  unfold Distinct at hD'
  obtain ⟨⟨ho₁o₂, ho₁a₁, ho₁c₂, ho₂a₁, ho₂c₂, ha₁c₂⟩, ⟨ho₂o₁, ha₁o₁, hc₂o₁, ha₁o₂, hc₂o₂, hc₂a₁⟩,
    ⟨ho₁t₂, ho₁r₁, ho₂t₂, ho₂r₁, ha₁t₂, ha₁r₁, hc₂t₂, hc₂r₁⟩, ht₂r₁, hndt₂, hndr₁⟩ := hD'
  have ha₁ : chans₀ a₁ = v :: chans₀' a₁ := by
    rw [hpop a₁, ChanMap.pushed_cons, ChanMap.pushed_not_mem ha₁r₁]; simp
  have hy : ∀ y, y ≠ a₁ → chans₀ y = ChanMap.pushed r₁ us y ++ chans₀' y := λ y hy => by
    rw [hpop y, ChanMap.pushed_cons]; simp [Ne.symm hy]
  have hsame : ∀ y, y ≠ a₁ → y ∉ r₁ → chans₀' y = chans₀ y := λ y h₁ h₂ => by
    rw [hy y h₁, ChanMap.pushed_not_mem h₂]; rfl
  -- The original channels after the step
  have e_y : ∀ y, y ≠ o₁ → chans₀' y ++ ChanMap.pushed [o₁] [v] y = chans₀' y := λ y hy => by
    simp [Ne.symm hy]
  have e_o₁ : chans₀' o₁ ++ ChanMap.pushed [o₁] [v] o₁ = chans₀ o₁ ++ [v] := by
    simp [hsame o₁ ho₁a₁ ho₁r₁]
  have e_o₂ := (e_y o₂ ho₂o₁).trans (hsame o₂ ho₂a₁ ho₂r₁)
  have e_c₂ := (e_y c₂ hc₂o₁).trans (hsame c₂ hc₂a₁ hc₂r₁)
  have e_a₁ := e_y a₁ ha₁o₁
  by_cases hab : (chans₀ o₁).length < (chans₀ o₂).length
  · -- The merged order fires
    have hm : min (chans₀ o₁).length (chans₀ o₂).length = (chans₀ o₁).length := by omega
    have hm' : min (chans₀ o₁ ++ [v]).length (chans₀ o₂).length = (chans₀ o₁).length + 1 := by
      simp only [List.length_append, List.length_singleton]; omega
    obtain ⟨w, W, hw⟩ := List.exists_cons_of_ne_nil
      (show (chans₀ o₂).drop (chans₀ o₁).length ≠ [] by
        intro h; have := congrArg List.length h; simp at this; omega)
    have hc₂ : chans₁ c₂ = w :: (W ++ chans₀ c₂) := by rw [hinv.ch_c₂, hm, hw]; rfl
    have hne : ∀ c ∈ t₂ ++ r₁, chans₁ c ≠ [] := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · have hX := hinv.x_t₂ c hc
        rw [hinv.other c (by rintro rfl; exact ho₁t₂ hc) (by rintro rfl; exact ho₂t₂ hc)
          (by rintro rfl; exact ha₁t₂ hc) (by rintro rfl; exact hc₂t₂ hc)]
        intro h
        rw [(List.append_eq_nil_iff.mp h).1] at hX
        simp at hX; omega
      · obtain ⟨u, hu⟩ := pushed_singleton hndr₁ hlen hc
        rw [hinv.other c (by rintro rfl; exact ho₁r₁ hc) (by rintro rfl; exact ho₂r₁ hc)
          (by rintro rfl; exact ha₁r₁ hc) (by rintro rfl; exact hc₂r₁ hc),
          hy c (by rintro rfl; exact ha₁r₁ hc), hu]
        simp
    have hnd : (c₂ :: (t₂ ++ r₁)).Nodup :=
      List.nodup_cons.mpr ⟨by simp [hc₂t₂, hc₂r₁],
        List.nodup_append.mpr ⟨hndt₂, hndr₁, λ a ha b hb hab => ht₂r₁ a ha (hab ▸ hb)⟩⟩
    refine ⟨_, λ y => (X y).tail, order_fire hmem hk hnd hc₂ hne,
      λ y h₁ h₂ => by simp [hinv.x_nil y h₁ h₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy'
      simp only [e_o₁, e_o₂, List.length_tail]
      have := hinv.x_t₂ y hy'
      simp only [List.length_append, List.length_singleton]; omega
    · intro y hy'
      simp only [e_o₁, e_o₂, List.length_tail]
      have := hinv.x_r₁ y hy'
      simp only [List.length_append, List.length_singleton]; omega
    · simp [hinv.ch_o₁, ho₁c₂, ho₁t₂, ho₁r₁, ho₁o₂]
    · simp only [e_o₁, e_o₂, hm']
      rw [take_succ_of_drop_eq_cons hw]
      simp [hinv.ch_o₂, hm, ho₂c₂, ho₂t₂, ho₂r₁]
    · simp only [e_o₁, e_a₁]
      simp [hinv.ch_a₁, ha₁, ha₁c₂, ha₁t₂, ha₁r₁, ha₁o₂]
    · simp only [e_o₁, e_o₂, e_c₂, hm']
      rw [drop_succ_of_drop_eq_cons hw]
      simp [hc₂, hc₂o₂]
    · intro y hy₁ hy₂ hy₃ hy₄
      simp only [e_y y hy₁]
      rw [hinv.other y hy₁ hy₂ hy₃ hy₄]
      by_cases hyt : y ∈ t₂
      · obtain ⟨x, X', hX⟩ := List.exists_cons_of_length_pos
          (show 0 < (X y).length by rw [hinv.x_t₂ y hyt]; omega)
        rw [hsame y hy₃ (ht₂r₁ y hyt)]
        simp [hy₂, hyt, hX]
      · by_cases hyr : y ∈ r₁
        · have hX : X y = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.x_r₁ y hyr]; omega)
          obtain ⟨u, hu⟩ := pushed_singleton hndr₁ hlen hyr
          rw [hy y hy₃, hu]
          simp [hy₂, hyr, hX]
        · rw [hsame y hy₃ hyr, hinv.x_nil y hyt hyr]
          simp [hy₂, hy₄, hyt, hyr]
  · -- Nothing to do on the rewritten side
    have hm : min (chans₀ o₁).length (chans₀ o₂).length = (chans₀ o₂).length := by omega
    have hm' : min (chans₀ o₁ ++ [v]).length (chans₀ o₂).length = (chans₀ o₂).length := by
      simp only [List.length_append, List.length_singleton]; omega
    refine ⟨chans₁, λ y => X y ++ ChanMap.pushed r₁ us y, .refl, ?_, ?_, ?_, hinv.ch_o₁,
      ?_, ?_, ?_, ?_⟩
    · intro y h₁ h₂
      simp [hinv.x_nil y h₁ h₂, ChanMap.pushed_not_mem h₂]
    · intro y hy'
      simp only [e_o₁, e_o₂, List.length_append, ChanMap.pushed_not_mem (ht₂r₁ y hy'),
        List.length_nil]
      have := hinv.x_t₂ y hy'; omega
    · intro y hy'
      obtain ⟨u, hu⟩ := pushed_singleton hndr₁ hlen hy'
      simp only [e_o₁, e_o₂, List.length_append, hu, List.length_singleton]
      have := hinv.x_r₁ y hy'; omega
    · simp only [e_o₁, e_o₂, hm']
      rw [hinv.ch_o₂, hm]
    · simp only [e_o₁, e_a₁]
      rw [hinv.ch_a₁, ha₁]; simp
    · simp only [e_o₁, e_o₂, e_c₂, hm']
      rw [hinv.ch_c₂, hm]
    · intro y hy₁ hy₂ hy₃ hy₄
      simp only [e_y y hy₁]
      rw [hinv.other y hy₁ hy₂ hy₃ hy₄, hy y hy₃, List.append_assoc]

private theorem inv_step_order₂ {L : AtomicProcs Op χ V} {k : Nat} [NeZero k]
  {chans₀ chans₀' chans₁ : ChanMap χ V} {X : χ → List V} {w : V} {ws : List V}
  (hD : Distinct o₁ o₂ a₁ c₂ t₂ r₁)
  (hmem : .async (.order k) (c₂ :: (t₂ ++ r₁)) [o₂] ∈ L)
  (hk : (c₂ :: (t₂ ++ r₁)).length = k)
  (hinv : Inv o₁ o₂ a₁ c₂ t₂ r₁ chans₀ chans₁ X)
  (hlen : t₂.length = ws.length)
  (hpop : ∀ y, chans₀ y = ChanMap.pushed (c₂ :: t₂) (w :: ws) y ++ chans₀' y) :
    ∃ chans₁' X', LocalTauStar L chans₁ L chans₁' ∧
      Inv o₁ o₂ a₁ c₂ t₂ r₁ (λ y => chans₀' y ++ ChanMap.pushed [o₂] [w] y) chans₁' X' := by
  have hD' := hD
  unfold Distinct at hD'
  obtain ⟨⟨ho₁o₂, ho₁a₁, ho₁c₂, ho₂a₁, ho₂c₂, ha₁c₂⟩, ⟨ho₂o₁, ha₁o₁, hc₂o₁, ha₁o₂, hc₂o₂, hc₂a₁⟩,
    ⟨ho₁t₂, ho₁r₁, ho₂t₂, ho₂r₁, ha₁t₂, ha₁r₁, hc₂t₂, hc₂r₁⟩, ht₂r₁, hndt₂, hndr₁⟩ := hD'
  have hc₂ : chans₀ c₂ = w :: chans₀' c₂ := by
    rw [hpop c₂, ChanMap.pushed_cons, ChanMap.pushed_not_mem hc₂t₂]; simp
  have hy : ∀ y, y ≠ c₂ → chans₀ y = ChanMap.pushed t₂ ws y ++ chans₀' y := λ y hy => by
    rw [hpop y, ChanMap.pushed_cons]; simp [Ne.symm hy]
  have hsame : ∀ y, y ≠ c₂ → y ∉ t₂ → chans₀' y = chans₀ y := λ y h₁ h₂ => by
    rw [hy y h₁, ChanMap.pushed_not_mem h₂]; rfl
  -- The original channels after the step
  have e_y : ∀ y, y ≠ o₂ → chans₀' y ++ ChanMap.pushed [o₂] [w] y = chans₀' y := λ y hy => by
    simp [Ne.symm hy]
  have e_o₂ : chans₀' o₂ ++ ChanMap.pushed [o₂] [w] o₂ = chans₀ o₂ ++ [w] := by
    simp [hsame o₂ ho₂c₂ ho₂t₂]
  have e_o₁ := (e_y o₁ ho₁o₂).trans (hsame o₁ ho₁c₂ ho₁t₂)
  have e_a₁ := (e_y a₁ ha₁o₂).trans (hsame a₁ ha₁c₂ ha₁t₂)
  have e_c₂ := e_y c₂ hc₂o₂
  by_cases hba : (chans₀ o₂).length < (chans₀ o₁).length
  · -- The merged order fires
    have hm : min (chans₀ o₁).length (chans₀ o₂).length = (chans₀ o₂).length := by omega
    have hm' : min (chans₀ o₁).length (chans₀ o₂ ++ [w]).length = (chans₀ o₂).length + 1 := by
      simp only [List.length_append, List.length_singleton]; omega
    have hc₂' : chans₁ c₂ = w :: chans₀' c₂ := by
      rw [hinv.ch_c₂, hm, List.drop_length, hc₂]; rfl
    have hne : ∀ c ∈ t₂ ++ r₁, chans₁ c ≠ [] := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨u, hu⟩ := pushed_singleton hndt₂ hlen hc
        rw [hinv.other c (by rintro rfl; exact ho₁t₂ hc) (by rintro rfl; exact ho₂t₂ hc)
          (by rintro rfl; exact ha₁t₂ hc) (by rintro rfl; exact hc₂t₂ hc),
          hy c (by rintro rfl; exact hc₂t₂ hc), hu]
        simp
      · have hX := hinv.x_r₁ c hc
        rw [hinv.other c (by rintro rfl; exact ho₁r₁ hc) (by rintro rfl; exact ho₂r₁ hc)
          (by rintro rfl; exact ha₁r₁ hc) (by rintro rfl; exact hc₂r₁ hc)]
        intro h
        rw [(List.append_eq_nil_iff.mp h).1] at hX
        simp at hX; omega
    have hnd : (c₂ :: (t₂ ++ r₁)).Nodup :=
      List.nodup_cons.mpr ⟨by simp [hc₂t₂, hc₂r₁],
        List.nodup_append.mpr ⟨hndt₂, hndr₁, λ a ha b hb hab => ht₂r₁ a ha (hab ▸ hb)⟩⟩
    refine ⟨_, λ y => (X y).tail, order_fire hmem hk hnd hc₂' hne,
      λ y h₁ h₂ => by simp [hinv.x_nil y h₁ h₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy'
      simp only [e_o₁, e_o₂, List.length_tail]
      have := hinv.x_t₂ y hy'
      simp only [List.length_append, List.length_singleton]; omega
    · intro y hy'
      simp only [e_o₁, e_o₂, List.length_tail]
      have := hinv.x_r₁ y hy'
      simp only [List.length_append, List.length_singleton]; omega
    · simp [hinv.ch_o₁, ho₁c₂, ho₁t₂, ho₁r₁, ho₁o₂]
    · simp only [e_o₁, e_o₂, hm']
      rw [List.take_of_length_le (by simp)]
      simp [hinv.ch_o₂, hm, ho₂c₂, ho₂t₂, ho₂r₁]
    · simp only [e_o₁, e_a₁]
      simp [hinv.ch_a₁, ha₁c₂, ha₁t₂, ha₁r₁, ha₁o₂]
    · simp only [e_o₁, e_o₂, e_c₂, hm']
      rw [List.drop_of_length_le (by simp)]
      simp [hc₂', hc₂o₂]
    · intro y hy₁ hy₂ hy₃ hy₄
      simp only [e_y y hy₂]
      rw [hinv.other y hy₁ hy₂ hy₃ hy₄]
      by_cases hyt : y ∈ t₂
      · have hX : X y = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.x_t₂ y hyt]; omega)
        obtain ⟨u, hu⟩ := pushed_singleton hndt₂ hlen hyt
        rw [hy y hy₄, hu]
        simp [hy₂, hyt, hX]
      · by_cases hyr : y ∈ r₁
        · obtain ⟨x, X', hX⟩ := List.exists_cons_of_length_pos
            (show 0 < (X y).length by rw [hinv.x_r₁ y hyr]; omega)
          rw [hsame y hy₄ hyt]
          simp [hy₂, hyr, hX]
        · rw [hsame y hy₄ hyt, hinv.x_nil y hyt hyr]
          simp [hy₂, hy₄, hyt, hyr]
  · -- Nothing to do on the rewritten side
    have hm : min (chans₀ o₁).length (chans₀ o₂).length = (chans₀ o₁).length := by omega
    have hm' : min (chans₀ o₁).length (chans₀ o₂ ++ [w]).length = (chans₀ o₁).length := by
      simp only [List.length_append, List.length_singleton]; omega
    refine ⟨chans₁, λ y => X y ++ ChanMap.pushed t₂ ws y, .refl, ?_, ?_, ?_, hinv.ch_o₁,
      ?_, ?_, ?_, ?_⟩
    · intro y h₁ h₂
      simp [hinv.x_nil y h₁ h₂, ChanMap.pushed_not_mem h₁]
    · intro y hy'
      obtain ⟨u, hu⟩ := pushed_singleton hndt₂ hlen hy'
      simp only [e_o₁, e_o₂, List.length_append, hu, List.length_singleton]
      have := hinv.x_t₂ y hy'; omega
    · intro y hy'
      have hy'' : y ∉ t₂ := λ h => ht₂r₁ y h hy'
      simp only [e_o₁, e_o₂, List.length_append, ChanMap.pushed_not_mem hy'',
        List.length_nil]
      have := hinv.x_r₁ y hy'; omega
    · simp only [e_o₁, e_o₂, hm']
      rw [hinv.ch_o₂, hm, List.take_append_of_le_length (by omega)]
    · simp only [e_o₁, e_a₁]
      exact hinv.ch_a₁
    · simp only [e_o₁, e_o₂, e_c₂, hm']
      rw [hinv.ch_c₂, hm, List.drop_append_of_le_length (by omega), hc₂]
      simp
    · intro y hy₁ hy₂ hy₃ hy₄
      simp only [e_y y hy₂]
      rw [hinv.other y hy₁ hy₂ hy₃ hy₄, hy y hy₄, List.append_assoc]

end Inv

end SyncOrderOrder

theorem sync_order_order_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ i₃ : Nat}
  {o : Op} {inputs : Vector χ (Arity.ι o)} {outputs : Vector χ (Arity.ω o)}
  {k₁ k₂ : Nat} [NeZero k₁] [NeZero k₂]
  {input₁ output₁ output₂ : χ} {rest₁ inputs₂ : List χ}
  [NeZero (inputs₂ ++ rest₁).length]
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.op o inputs outputs))
  (h₂ : proc.atoms[i₂]? = some (.async (.order k₁) (input₁ :: rest₁) [output₁]))
  (h₃ : proc.atoms[i₃]? = some (.async (.order k₂) inputs₂ [output₂]))
  (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
  (hlen₁ : (input₁ :: rest₁).length = k₁) (hlen₂ : inputs₂.length = k₂)
  (hmem₁ : output₁ ∈ inputs) (hmem₂ : output₂ ∈ inputs) :
    RuleOK proc [i₃, i₂, i₁] [
      .op o (inputs.replace output₁ input₁) outputs,
      .order (inputs₂ ++ rest₁).toVector output₂,
    ]
  := by
  open SyncOrderOrder in
  -- `inputs₂` is non-empty
  obtain ⟨head₂, tail₂, rfl⟩ : ∃ c t, inputs₂ = c :: t := by
    cases inputs₂ with
    | nil => exact absurd hlen₂.symm (NeZero.ne k₂)
    | cons c t => exact ⟨c, t, rfl⟩
  have hP : matchedOf proc.atoms [i₃, i₂, i₁] = [
      .async (.order k₂) (head₂ :: tail₂) [output₂],
      .async (.order k₁) (input₁ :: rest₁) [output₁],
      .op o inputs outputs] := by
    simp [h₁, h₂, h₃]
  have hmem_order : (.async (.order ((head₂ :: tail₂) ++ rest₁).length)
      (head₂ :: (tail₂ ++ rest₁)) [output₂] : AtomicProc Op χ V) ∈
      ([.op o (inputs.replace output₁ input₁) outputs,
        .order ((head₂ :: tail₂) ++ rest₁).toVector output₂] : AtomicProcs Op χ V) :=
    List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  -- Facts from affineness
  have hm₁ : output₁ ∈ inputs.toList := by simpa using hmem₁
  have hm₂ : output₂ ∈ inputs.toList := by simpa using hmem₂
  have hnd₁ := haff.atom_nodup h₁
  have hnd₂ := (haff.atom_nodup h₂).1
  have hnd₃ := (haff.atom_nodup h₃).1
  simp only [AtomicProc.inputs_op, AtomicProc.outputs_op, AtomicProc.inputs_async] at hnd₁ hnd₂ hnd₃
  have hdj₂₁ := haff.atom_disjoint h₂ h₁ hne₂₁
  have hdj₃₁ := haff.atom_disjoint h₃ h₁ hne₃₁
  have hdj₃₂ := haff.atom_disjoint h₃ h₂ hne₃₂
  simp only [AtomicProc.inputs_op, AtomicProc.outputs_op, AtomicProc.inputs_async,
    AtomicProc.outputs_async] at hdj₂₁ hdj₃₁ hdj₃₂
  have hc₂t₂ : head₂ ∉ tail₂ := (List.nodup_cons.mp hnd₃).1
  have ha₁r₁ : input₁ ∉ rest₁ := (List.nodup_cons.mp hnd₂).1
  have ht₂ : ∀ y ∈ tail₂, y ∉ inputs.toList := λ y hy => hdj₃₁.1 (List.mem_cons_of_mem _ hy)
  have hr₁ : ∀ y ∈ rest₁, y ∉ inputs.toList := λ y hy => hdj₂₁.1 (List.mem_cons_of_mem _ hy)
  have ha₁ : input₁ ∉ inputs.toList := hdj₂₁.1 (List.mem_cons_self ..)
  have hc₂ : head₂ ∉ inputs.toList := hdj₃₁.1 (List.mem_cons_self ..)
  have ho₁ : output₁ ∉ outputs.toList := hdj₂₁.2 (List.mem_singleton_self _)
  have ho₂ : output₂ ∉ outputs.toList := hdj₃₁.2 (List.mem_singleton_self _)
  have hD : Distinct output₁ output₂ input₁ head₂ tail₂ rest₁ :=
    distinct_of
      (λ h => hdj₃₂.2 (List.mem_singleton_self _) (by simp [h]))
      (λ h => ha₁ (h ▸ hm₁)) (λ h => hc₂ (h ▸ hm₁))
      (λ h => ha₁ (h ▸ hm₂)) (λ h => hc₂ (h ▸ hm₂))
      (λ h => hdj₃₂.1 (List.mem_cons_self ..) (by simp [h]))
      (λ h => ht₂ _ h hm₁) (λ h => hr₁ _ h hm₁) (λ h => ht₂ _ h hm₂) (λ h => hr₁ _ h hm₂)
      (λ h => hdj₃₂.1 (List.mem_cons_of_mem _ h) (List.mem_cons_self ..)) ha₁r₁ hc₂t₂
      (λ h => hdj₃₂.1 (List.mem_cons_self ..) (List.mem_cons_of_mem _ h))
      (λ y hy hr => hdj₃₂.1 (List.mem_cons_of_mem _ hy) (List.mem_cons_of_mem _ hr))
      (List.nodup_cons.mp hnd₃).2 (List.nodup_cons.mp hnd₂).2
  have hD' := hD
  unfold Distinct at hD'
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₃, i₂, i₁] ∧
    L₁ = [.op o (inputs.replace output₁ input₁) outputs,
      .order ((head₂ :: tail₂) ++ rest₁).toVector output₂] ∧
    ∃ X, Inv output₁ output₂ input₁ head₂ tail₂ rest₁ chans₀ chans₁ X, ?_, ?_⟩
  · constructor
    · simp [hne₂₁, hne₃₁, hne₃₂]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1,
        (List.getElem?_eq_some_iff.mp h₃).1]
    · simp only [AtomicProcs.inputNames_cons, AtomicProcs.inputNames_nil, AtomicProc.inputs_op,
        AtomicProc.order, AtomicProc.inputs_async, vector_toList_replace, List.append_nil]
      refine List.nodup_append.mpr ⟨nodup_replace hnd₁.1 ha₁, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨by simp [hD'], List.nodup_append.mpr
          ⟨hD'.2.2.2.2.1, hD'.2.2.2.2.2, λ a ha b hb hab => hD'.2.2.2.1 a ha (hab ▸ hb)⟩⟩
      · intro a ha b hb hab
        subst hab
        simp only [toList_toVector', List.mem_cons, List.mem_append] at hb
        rcases mem_of_mem_replace ha with ha | rfl
        · rcases hb with (rfl | hb) | hb
          · exact hc₂ ha
          · exact ht₂ _ hb ha
          · exact hr₁ _ hb ha
        · simp [hD'] at hb
    · simp only [AtomicProcs.outputNames_cons, AtomicProcs.outputNames_nil, AtomicProc.outputs_op,
        AtomicProc.order, AtomicProc.outputs_async, List.append_nil]
      exact List.nodup_append.mpr ⟨hnd₁.2, by simp, λ a ha b hb hab => by
        simp at hb; subst hb; subst hab; exact ho₂ ha⟩
    · intro x hx
      left
      simp only [AtomicProcs.inputNames_cons, AtomicProcs.inputNames_nil, AtomicProc.inputs_op,
        AtomicProc.order, AtomicProc.inputs_async, vector_toList_replace, toList_toVector',
        List.append_nil, List.mem_append] at hx
      rcases hx with hx | hx
      · rcases mem_of_mem_replace hx with hx | rfl
        · simp [hP, hx]
        · simp [hP]
      · simp only [List.mem_cons] at hx
        rcases hx with (rfl | hx) | hx
        · simp [hP]
        · simp [hP, hx]
        · simp [hP, hx]
    · intro x hx
      left
      simp only [AtomicProcs.outputNames_cons, AtomicProcs.outputNames_nil, AtomicProc.outputs_op,
        AtomicProc.order, AtomicProc.outputs_async, List.append_nil, List.mem_append,
        List.mem_singleton] at hx
      rcases hx with hx | rfl
      · simp [hP, hx]
      · simp [hP]
  · constructor
    · exact ⟨rfl, rfl, λ _ => [], inv_init⟩
    · rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, rfl, X, hinv⟩ hpop
      -- `x` is read by the context, so it is none of the matched inputs
      have hx' : ∀ y, y ∈ AtomicProcs.inputNames (matchedOf proc.atoms [i₃, i₂, i₁]) → x ≠ y :=
        λ y hy h => hx (h ▸ hy)
      obtain ⟨chans₁', hpop', hinv'⟩ := inv_frame_pop hD hinv
        (hx' _ (by simp [hP, hm₁])) (hx' _ (by simp [hP, hm₂])) (hx' _ (by simp [hP]))
        (hx' _ (by simp [hP])) (λ h => hx (by simp [hP, h])) (λ h => hx (by simp [hP, h])) hpop
      exact ⟨chans₁', hpop', rfl, rfl, X, hinv'⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals hlen hx hnd hfp ⟨rfl, rfl, X, hinv⟩
      have ho₁' : output₁ ∉ outs := λ h => by simpa [hP] using (hx _ h).1
      have ho₂' : output₂ ∉ outs := λ h => by simpa [hP] using (hx _ h).1
      exact ⟨rfl, rfl, X, inv_frame_push hinv ho₁' ho₂'⟩
    · rintro L₀ chans₀ L₁ chans₁ op ins outs inVals outVals chans₀' _ _ ⟨rfl, rfl, X, hinv⟩
        hmem hpop
      -- The op fires: the rewritten op reads `input₁` instead of `output₁`, with the same values
      rw [hP] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        AtomicProc.op.injEq] at hmem
      obtain ⟨e, hins, houts⟩ := hmem
      have e' := e.symm
      subst e'
      have e₁ := (eq_of_heq hins).symm
      have e₂ := (eq_of_heq houts).symm
      subst e₁ e₂
      have ⟨hpop₁, hinv₁⟩ := inv_step_op hD hinv hnd₁.1 (by simp) hm₁ hm₂ ha₁ hc₂ ht₂ hr₁ hpop
      refine ⟨inputs.replace output₁ input₁, outputs, canon output₁ output₂ input₁ head₂ chans₀' X,
        List.mem_cons_self .., ?_, rfl, rfl, X, inv_frame_push hinv₁ ho₁ ho₂⟩
      intro y
      rw [vector_toList_replace]
      exact hpop₁ y
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs' outputs' inputVals outputVals chans₀' _ _ ⟨rfl, rfl, X, hinv⟩
        hget hinterp hlen _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        -- `order₂` fires
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, w, ws, rfl, rfl⟩ := hinterp.order_inv
        obtain ⟨chans₁', X', hstep, hinv'⟩ :=
          inv_step_order₂ hD hmem_order rfl hinv (by simpa using hlen) hpop
        exact ⟨_, chans₁', hstep, by simp, rfl, X', hinv'⟩
      | 1, hget =>
        -- `order₁` fires
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, v, us, rfl, rfl⟩ := hinterp.order_inv
        obtain ⟨chans₁', X', hstep, hinv'⟩ :=
          inv_step_order₁ hD hmem_order rfl hinv (by simpa using hlen) hpop
        exact ⟨_, chans₁', hstep, by simp, rfl, X', hinv'⟩
      | 2, hget => simp at hget -- The op is not async
      | n + 3, hget => simp at hget
  · rintro L₁ chans₁ ⟨_, rfl, X, hinv⟩
    exact ⟨rfl, inv_empty hinv⟩

end Wavelet.Compile.DeadCodeElim
