import Batteries.Data.Vector.Lemmas
import Mathlib.Data.List.Nodup

import Wavelet.Data.List
import Wavelet.Data.Vector

/-! Definition and lemmas for channel maps. -/

namespace Wavelet.Dataflow

abbrev ChanMap χ V := χ → List V

def ChanMap.empty : ChanMap χ V := λ _ => []

def ChanMap.pushVal [DecidableEq χ] (name : χ) (val : V) (map : ChanMap χ V) : ChanMap χ V :=
  λ n => if n = name then map n ++ [val] else map n

def ChanMap.pushVals [DecidableEq χ]
  (names : Vector χ n) (vals : Vector V n)
  (map : ChanMap χ V) : ChanMap χ V :=
  (names.zip vals).foldl (λ map (n, v) => map.pushVal n v) map

def ChanMap.popVal
  {χ : Type u}
  [DecidableEq χ]
  (name : χ)
  (map : ChanMap χ V) : Option (V × ChanMap χ V) :=
  match map name with
  | [] => none
  | v :: vs => some (v, λ n => if n = name then vs else map n)

def ChanMap.popVals
  {χ : Type u} {V : Type v}
  [DecidableEq χ]
  (names : Vector χ n)
  (map : ChanMap χ V) : Option (Vector V n × ChanMap χ V)
  := match n with
  | 0 => some (#v[], map)
  | _ + 1 => do
    let (vals', map') ← map.popVals names.pop
    let (val, map'') ← map'.popVal names.back
    return (vals'.push val, map'')

def ChanMap.IsSingleton (name : χ) (val : V) (map : ChanMap χ V) : Prop := map name = [val]

def ChanMap.IsEmpty (name : χ) (map : ChanMap χ V) : Prop := map name = []

def ChanMap.getBuf (name : χ) (map : ChanMap χ V) : List V := map name

def ChanMap.Pairwise
  (P : V → V → Prop)
  (map : ChanMap χ V) : Prop :=
  ∀ {x₁ x₂} {i : Nat} {j : Nat},
    x₁ ≠ x₂ ∨ i ≠ j →
    (_ : i < (map x₁).length) →
    (_ : j < (map x₂).length) →
    P (map x₁)[i] (map x₂)[j]

/-! Lemmas about `ChanMap`. -/
section Lemmas

theorem push_vals_disjoint [DecidableEq χ]
  {map : ChanMap χ V}
  {names : Vector χ n}
  (hdisj : name ∉ names) :
  map.pushVals names vals name = map name
:= by
  simp [ChanMap.pushVals]
  induction n generalizing map with
  | zero => simp [Vector.eq_empty]
  | succ n' ih =>
    rw [← (Vector.push_pop_back (names.zip vals))]
    rw [Vector.foldl_push]
    simp [ChanMap.pushVal]
    split <;> rename_i h₁
    · simp [h₁] at hdisj
    · simp [Vector.pop_zip]
      rw [ih]
      intros h
      have := Vector.mem_pop_iff.mpr (.inl h)
      exact False.elim (hdisj this)

theorem push_vals_map [DecidableEq χ]
  {map₁ map₂ : ChanMap χ V}
  {names : Vector χ n}
  {f : χ → χ}
  (hinj : Function.Injective f)
  (heq : map₁ (f name) = map₂ name) :
  map₁.pushVals (names.map f) vals (f name) =
  map₂.pushVals names vals name
:= by
  simp [ChanMap.pushVals]
  induction n generalizing map₁ map₂ name with
  | zero =>
    simp [Vector.eq_empty, heq]
  | succ n' ih =>
    rw [← (Vector.push_pop_back (names.zip vals))]
    rw [← (Vector.push_pop_back ((names.map f).zip vals))]
    rw [Vector.foldl_push]
    rw [Vector.foldl_push]
    simp [ChanMap.pushVal]
    split <;> rename_i h₁
    · simp [hinj h₁]
      simp [Vector.pop_zip]
      rw [← Vector.map_pop]
      apply ih
      simp [hinj h₁] at heq
      exact heq
    · have h₂ := (Function.Injective.ne_iff hinj).mp h₁
      simp [h₂]
      simp [Vector.pop_zip]
      rw [← Vector.map_pop]
      apply ih
      exact heq

theorem push_val_empty [DecidableEq χ]
  {map : ChanMap χ V}
  (hempty : map name = []) :
  map.pushVal name val = λ n => if n = name then [val] else map n := by
  funext name'
  simp [ChanMap.pushVal]
  split
  · rename_i h
    simp [h, hempty]
  · rfl

theorem push_vals_empty [DecidableEq χ]
  {map : ChanMap χ V}
  {names : Vector χ n}
  {vals : Vector V n}
  (hnodup : names.toList.Nodup)
  (hempty : ∀ name ∈ names, map name = []) :
  map.pushVals names vals =
    λ n => if let some i := names.finIdxOf? n then [vals[i]]
    else map n := by
  funext name'
  simp [ChanMap.pushVals]
  unfold ChanMap.pushVal
  induction n with
  | zero =>
    have : names.zip vals = #v[] := by simp
    simp [this, Vector.finIdxOf?_empty]
  | succ n' ih =>
    have : names.zip vals = (names.pop.zip vals.pop).push (names.back, vals.back)
    := by
      apply Vector.toList_inj.mp
      simp [Vector.zip_eq_zipWith, Vector.toList_zipWith,
        Vector.toList_push, Vector.toList_pop]
      have :
        [(names.back, vals.back)] =
        [names.back].zipWith Prod.mk [vals.back]
      := by simp
      rw [this, ← List.zipWith_append (by simp)]
      simp [← Vector.toList_pop, ← Vector.toList_push]
    rw [this, Vector.foldl_push]
    simp
    specialize ih
      (vals := vals.pop)
      (Vector.nodup_implies_pop_nodup hnodup)
      _
    · intros name hname
      apply hempty name (Vector.mem_pop_implies_mem hname)
    · simp only [ih]
      split_ifs <;> rename_i h₁
      · split <;> rename_i h₂
        · have := Vector.nodup_implies_back_not_mem_pop hnodup
          simp [Vector.finIdxOf?_eq_none_iff.mpr this, h₁] at h₂
        · simp [hempty name' (by simp [h₁])]
          simp [h₁, Vector.back]
          rw [(Vector.finIdxOf?_eq_some_iff (i := ⟨n', by omega⟩)).mpr _]
          simp [Vector.get]
          intros j hj h
          rw [← Vector.getElem_toList (by simp)] at h
          rw [← Vector.getElem_toList (by simp)] at h
          have := (List.Nodup.getElem_inj_iff hnodup).mp h
          omega
      · simp
        split <;> rename_i h₂
        · rename_i i
          simp [Vector.get] at h₂
          rw [(Vector.finIdxOf?_eq_some_iff (i := ⟨↑i, by omega⟩) (a := name')).mpr]
          constructor
          · simp [Vector.get, h₂]
          · simp [Vector.get]
            intros j hj
            have := h₂.2 ⟨↑j, (by omega)⟩ hj
            simp at this
            exact this
        · have := Option.eq_none_iff_forall_ne_some.mpr h₂
          simp at this
          have : name' ∉ names := by
            simp [Vector.mem_pop_iff, h₁, this]
          simp [Vector.finIdxOf?_eq_none_iff.mpr this]

theorem pop_vals_unfold [DecidableEq χ]
  {map : ChanMap χ V}
  {names : Vector χ (n + 1)} :
    map.popVals names = do
      let (vals', map') ← map.popVals names.pop
      let (val, map'') ← map'.popVal names.back
      return (vals'.push val, map'')
  := by rfl

theorem push_vals_unfold [DecidableEq χ]
  {map : ChanMap χ V}
  {names : Vector χ (n + 1)}
  {vals : Vector V (n + 1)} :
    map.pushVals names vals =
      (map.pushVals names.pop vals.pop).pushVal names.back vals.back
  := by
  cases names using Vector.back_induction with | push =>
  cases vals using Vector.back_induction with | push =>
  simp [ChanMap.pushVals, Vector.push_zip]

theorem pop_val_singleton [DecidableEq χ]
  {map : ChanMap χ V}
  (hsingleton : map name = [val]) :
  ∃ map',
    map.popVal name = some (val, map') ∧
    map' = λ n => if n = name then [] else map n := by
  simp [ChanMap.popVal, hsingleton]

theorem pop_vals_singleton [DecidableEq χ]
  {map : ChanMap χ V}
  {names : Vector χ n}
  (prop : χ → V → Prop)
  (hnodup : names.toList.Nodup)
  (hsingletons : ∀ name ∈ names, ∃ val, map name = [val] ∧ prop name val) :
  ∃ map' vals,
    map.popVals names = some (vals, map') ∧
    map' = (λ n => if n ∈ names then [] else map n) ∧
    List.Forall₂ prop names.toList vals.toList
  := by
  induction n with
  | zero => simp [Vector.eq_empty, ChanMap.popVals]
  | succ n' ih =>
    have : names = names.pop.push names.back := by simp
    rw [this]
    simp [ChanMap.popVals, Option.bind, bind]
    specialize ih (Vector.nodup_implies_pop_nodup hnodup) _
    · intros name hname
      exact hsingletons name (Vector.mem_pop_implies_mem hname)
    · have ⟨map'', vals', h₁, h₂, h₃⟩ := ih
      have ⟨val, h₄, h₅⟩ := hsingletons names.back (by simp)
      have h₆ : names.back ∉ names.pop :=
        Vector.nodup_implies_back_not_mem_pop hnodup
      simp [h₁, ChanMap.popVal, h₂, h₄, h₆]
      constructor
      · funext name'
        split <;> rename_i h₇
        · simp [h₇]
        · split <;> rename_i h₈
          · simp [Vector.mem_pop_implies_mem h₈]
          · simp [Vector.mem_pop_iff, h₇, h₈]
      · rw [← Vector.push_pop_back names]
        simp only [Vector.toList_push]
        apply List.forall₂_iff_get.mpr
        constructor
        · simp
        · intros i _ _
          simp [List.getElem_append]
          split <;> rename_i h₈
          · have := (List.forall₂_iff_get.mp h₃).2 i
              (by simp; assumption) (by simp; assumption)
            simp at this
            exact this
          · exact h₅

theorem pop_val_to_pop_vals [DecidableEq χ]
  {map : ChanMap χ V}
  (hpop_val : map.popVal name = some (val, map')) :
    map.popVals #v[name] = some (#v[val], map')
  := by simp [ChanMap.popVals, hpop_val]

theorem pop_vals_append [DecidableEq χ]
  {map : ChanMap χ V}
  {names₁ : Vector χ n₁}
  {names₂ : Vector χ n₂}
  (hpop₁ : map.popVals names₁ = some (vals₁, map'))
  (hpop₂ : map'.popVals names₂ = some (vals₂, map'')) :
    map.popVals (names₁ ++ names₂) = some (vals₁ ++ vals₂, map'')
  := by
  induction names₂ using Vector.back_induction
    generalizing map'' with
  | empty =>
    simp [ChanMap.popVals] at hpop₂
    simp [Vector.eq_empty, hpop₁, hpop₂]
  | push _ _ ih =>
    simp [pop_vals_unfold, Option.bind] at hpop₂
    split at hpop₂; contradiction
    rename_i res₁ heq₁
    cases res₁
    simp at hpop₂
    split at hpop₂; contradiction
    rename_i res₂ heq₂
    cases res₂
    simp at hpop₂
    have := ih heq₁
    simp [pop_vals_unfold, this, heq₂, hpop₂]

@[simp]
theorem pop_vals_zero
  [DecidableEq χ]
  {chans : ChanMap χ V} : chans.popVals #v[] = some (#v[], chans)
  := by simp [ChanMap.popVals, Vector.eq_empty]

@[simp]
theorem push_vals_zero
  [DecidableEq χ]
  {chans : ChanMap χ V} : chans.pushVals #v[] vals₁ = chans
  := by rfl

theorem pop_val_push_val_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hpop : chans.popVal name₂ = some (val₂, chans')) :
    (chans.pushVal name₁ val₁).popVal name₂ =
      some (val₂, chans'.pushVal name₁ val₁)
  := by
  simp [ChanMap.popVal, ChanMap.pushVal] at hpop ⊢
  split at hpop; contradiction
  rename_i hpop'
  by_cases h₁ : name₁ = name₂
  · subst h₁
    simp at hpop ⊢
    simp [hpop', ← hpop]
    funext
    simp [ChanMap.pushVal]
    grind only [cases Or]
  · simp [Ne.symm h₁] at hpop ⊢
    simp [hpop', ← hpop]
    funext
    simp [ChanMap.pushVal]
    grind only [cases Or]

theorem pop_vals_push_val_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hpop : chans.popVals names₂ = some (vals₂, chans')) :
    (chans.pushVal name₁ val₁).popVals names₂ =
      some (vals₂, chans'.pushVal name₁ val₁)
  := by
  induction names₂ using Vector.back_induction
    generalizing chans' with
  | empty =>
    simp [Vector.eq_empty, ChanMap.popVals] at hpop ⊢
    simp [hpop]
  | push names₂' name₂ ih =>
    simp [pop_vals_unfold, Option.bind] at hpop
    split at hpop; contradiction
    rename_i res₁ heq₁
    simp at hpop
    split at hpop; contradiction
    rename_i res₂ heq₂
    cases res₂
    simp at hpop
    specialize ih heq₁
    simp [pop_vals_unfold, ih,
      pop_val_push_val_commute heq₂, hpop]

/-- If a list of channels already have values ready to pop,
then it can commute with any `pushVals` operation. -/
theorem pop_vals_push_vals_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hpop : chans.popVals names₂ = some (vals₂, chans')) :
    (chans.pushVals names₁ vals₁).popVals names₂ =
      some (vals₂, chans'.pushVals names₁ vals₁)
  := by
  induction names₁ using Vector.back_induction
    generalizing chans' with
  | empty => simp [push_vals_zero, hpop]
  | push names₂' name₂ ih =>
    simp [push_vals_unfold]
    specialize ih hpop (vals₁ := vals₁.pop)
    exact pop_vals_push_val_commute ih

theorem pop_val_pop_val_disj_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hdisj : name₁ ≠ name₂)
  (hpop₁ : chans.popVal name₁ = some (val₁, chans₁))
  (hpop₂ : chans.popVal name₂ = some (val₂, chans₂)) :
    ∃ chans',
      chans₁.popVal name₂ = some (val₂, chans') ∧
      chans₂.popVal name₁ = some (val₁, chans')
  := by
  simp [ChanMap.popVal] at hpop₁ hpop₂ ⊢
  split at hpop₁; contradiction
  rename_i rest₁ heq₁
  simp at hpop₁
  split at hpop₂; contradiction
  rename_i rest₂ heq₂
  simp at hpop₂
  exists λ n =>
    if n = name₁ then rest₁
    else if n = name₂ then rest₂
    else chans n
  simp [← hpop₁, ← hpop₂, hdisj, Ne.symm hdisj, heq₁, heq₂]
  funext
  grind only

theorem pop_val_pop_vals_disj_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hdisj : name₁ ∉ names₂)
  (hpop₁ : chans.popVal name₁ = some (val₁, chans₁))
  (hpop₂ : chans.popVals names₂ = some (vals₂, chans₂)) :
    ∃ chans',
      chans₁.popVals names₂ = some (vals₂, chans') ∧
      chans₂.popVal name₁ = some (val₁, chans')
  := by
  induction names₂ using Vector.back_induction
    generalizing chans₁ chans₂ with
  | empty =>
    simp [Vector.eq_empty] at hpop₂ ⊢
    subst hpop₂
    exact hpop₁
  | push names₂' name₂ ih =>
    simp [pop_vals_unfold, Option.bind] at hpop₂
    split at hpop₂; contradiction
    rename_i res₁ heq₁
    rcases res₁ with ⟨vals₂', chans₂'⟩
    simp at hpop₂
    split at hpop₂; contradiction
    rename_i res₂ heq₂
    rcases res₂ with ⟨val₂, chans₂''⟩
    simp at hpop₂
    simp at hdisj
    have ⟨chans', hpop₁₂, hpop₂₁⟩ := ih hdisj.1 hpop₁ heq₁
    have ⟨chans'', hpop₁₂', hpop₂₁'⟩ := pop_val_pop_val_disj_commute hdisj.2 hpop₂₁ heq₂
    exists chans''
    constructor
    · simp [pop_vals_unfold, hpop₁₂, hpop₁₂', hpop₂]
    · simp [← hpop₂, hpop₂₁']

theorem pop_vals_pop_vals_disj_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hdisj : names₁.toList.Disjoint names₂.toList)
  (hpop₁ : chans.popVals names₁ = some (vals₁, chans₁))
  (hpop₂ : chans.popVals names₂ = some (vals₂, chans₂)) :
    ∃ chans',
      chans₁.popVals names₂ = some (vals₂, chans') ∧
      chans₂.popVals names₁ = some (vals₁, chans')
  := by
  induction names₁ using Vector.back_induction
    generalizing chans₁ chans₂ with
  | empty =>
    simp [Vector.eq_empty] at hpop₁ ⊢
    subst hpop₁
    exact hpop₂
  | push names₁' name₁ ih =>
    simp [pop_vals_unfold, Option.bind] at hpop₁
    split at hpop₁; contradiction
    rename_i res₁ heq₁
    rcases res₁ with ⟨vals₁', chans₁'⟩
    simp at hpop₁
    split at hpop₁; contradiction
    rename_i res₂ heq₂
    rcases res₂ with ⟨val₁, chans₁''⟩
    simp at hpop₁
    simp [Vector.toList_push] at hdisj
    have ⟨chans', hpop₁₂, hpop₂₁⟩ := ih hdisj.1 heq₁ hpop₂
    have ⟨chans'', hpop₁₂', hpop₂₁'⟩ := pop_val_pop_vals_disj_commute hdisj.2 heq₂ hpop₁₂
    exists chans''
    constructor
    · simp [← hpop₁]
      exact hpop₁₂'
    · simp [pop_vals_unfold, hpop₂₁, hpop₂₁', hpop₁]

theorem push_val_push_val_disj_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hdisj : name₁ ≠ name₂) :
    (chans.pushVal name₁ val₁).pushVal name₂ val₂
      = (chans.pushVal name₂ val₂).pushVal name₁ val₁
  := by
  funext name
  simp [ChanMap.pushVal]
  grind only

theorem push_val_push_vals_disj_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hdisj : name₁ ∉ names₂) :
    (chans.pushVal name₁ val₁).pushVals names₂ vals₂
      = (chans.pushVals names₂ vals₂).pushVal name₁ val₁
  := by
  induction names₂ using Vector.back_induction
    generalizing chans with
  | empty => simp
  | push names₂' name₂ ih =>
    simp [push_vals_unfold]
    simp at hdisj
    rw [ih hdisj.1]
    rw [push_val_push_val_disj_commute hdisj.2]

theorem push_vals_push_vals_disj_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hdisj : names₁.toList.Disjoint names₂.toList) :
    (chans.pushVals names₁ vals₁).pushVals names₂ vals₂
      = (chans.pushVals names₂ vals₂).pushVals names₁ vals₁
  := by
  induction names₁ using Vector.back_induction
    generalizing chans with
  | empty => simp
  | push names₁' name₁ ih =>
    simp [push_vals_unfold]
    simp [Vector.toList_push] at hdisj
    rw [push_val_push_vals_disj_commute hdisj.2]
    rw [ih hdisj.1]

theorem pop_vals_eq_head [DecidableEq χ]
  {map : ChanMap χ V}
  {names₁ names₂ : Vector χ n}
  (hhead₁ : names₁.toList = name :: names₁')
  (hhead₂ : names₂.toList = name :: names₂')
  (hpop₁ : map.popVals names₁ = some (vals₁, map'))
  (hpop₂ : map.popVals names₂ = some (vals₂, map'')) :
    vals₁.toList.head? = vals₂.toList.head?
  := by
  cases n with
  | zero => simp [Vector.eq_empty]
  | succ n' =>
    simp [pop_vals_unfold, Option.bind] at hpop₁ hpop₂
    split at hpop₁; contradiction
    rename_i heq₁
    split at hpop₂; contradiction
    rename_i heq₂
    cases n' with
    | zero =>
      simp [Vector.eq_empty] at heq₁ heq₂ hpop₁ hpop₂
      simp [heq₁] at heq₂
      subst heq₂
      split at hpop₁; contradiction
      rename_i heq₁'
      split at hpop₂; contradiction
      rename_i heq₂'
      simp only [Option.some.injEq, Prod.mk.injEq] at hpop₁ hpop₂
      simp [← hpop₁, ← hpop₂]
      have : names₁.back = names₂.back := by
        simp [Vector.back, ← Vector.getElem_toList, hhead₁, hhead₂]
      simp [this] at heq₁' heq₂'
      simp [heq₁'] at heq₂'
      simp [heq₂']
    | succ =>
      have hne₁ : names₁' ≠ [] := by
        intros h
        simp [h] at hhead₁
        have : names₁.toList.length = 1 := by simp [hhead₁]
        simp at this
      have hne₂ : names₂' ≠ [] := by
        intros h
        simp [h] at hhead₂
        have : names₂.toList.length = 1 := by simp [hhead₂]
        simp at this
      have hhead₁' : names₁.pop.toList = name :: names₁'.dropLast := by
        simp [Vector.toList_pop, hhead₁,
          List.dropLast_cons_of_ne_nil hne₁]
      have hhead₂' : names₂.pop.toList = name :: names₂'.dropLast := by
        simp [Vector.toList_pop, hhead₂,
          List.dropLast_cons_of_ne_nil hne₂]
      have := pop_vals_eq_head hhead₁' hhead₂' heq₁ heq₂
      simp at hpop₁ hpop₂
      split at hpop₁; contradiction
      rename_i heq₁'
      split at hpop₂; contradiction
      rename_i heq₂'
      simp at hpop₁ hpop₂
      simp only [← hpop₁, ← hpop₂, Vector.toList_push]
      simp [List.head?_eq_head] at this ⊢
      exact this

@[simp]
theorem ChanMap.pairwise_empty
  (P : V → V → Prop) : (ChanMap.empty (χ := χ)).Pairwise P := by
  intros x₁ x₂ i j hne hi hj
  simp [ChanMap.empty] at hi

theorem pop_val_monotone [DecidableEq χ]
  {map : ChanMap χ V}
  (hpop : map.popVal name = some (val, map')) :
    ∀ name', map' name' ⊆ map name'
  := by
  intros name'
  simp [ChanMap.popVal] at hpop
  split at hpop; contradiction
  rename_i rest heq
  simp at hpop
  by_cases h : name' = name
  · subst h
    simp [← hpop, heq]
  · simp [← hpop, h]

theorem pop_vals_monotone [DecidableEq χ]
  {map : ChanMap χ V}
  {names : Vector χ n}
  (hpop : map.popVals names = some (vals, map')) :
    ∀ name', map' name' ⊆ map name'
  := by
  induction names using Vector.back_induction
    generalizing map' with
  | empty =>
    simp at hpop
    simp [hpop]
  | push names' name ih =>
    intros name'
    simp [pop_vals_unfold, Option.bind] at hpop
    split at hpop; contradiction
    rename_i res₁ heq₁
    rcases res₁ with ⟨vals', map''⟩
    simp at hpop
    split at hpop; contradiction
    rename_i res₂ heq₂
    rcases res₂ with ⟨val, map'''⟩
    simp at hpop
    specialize ih heq₁ name'
    have := pop_val_monotone heq₂ name'
    simp [hpop] at this
    exact List.Subset.trans this ih

theorem pop_vals_exists_get_index [DecidableEq χ]
  {map : ChanMap χ V}
  (hpop : map.popVals names = some (vals, map'))
  (hmem : v ∈ vals) :
    ∃ name ∈ names, v ∈ map name
  := by
  induction names using Vector.back_induction
    generalizing map' with
  | empty => simp [Vector.eq_empty] at hmem
  | push names' name ih =>
    simp [pop_vals_unfold, Option.bind] at hpop
    split at hpop; contradiction
    rename_i res₁ heq₁
    rcases res₁ with ⟨vals', map''⟩
    simp at hpop
    split at hpop; contradiction
    rename_i res₂ heq₂
    rcases res₂ with ⟨val, map'''⟩
    simp at hpop
    simp [← hpop] at hmem
    cases hmem with
    | inl hmem' =>
      have ⟨name, hname, hv⟩ := ih heq₁ hmem'
      exists name
      simp [hname, hv]
    | inr h =>
      subst h
      exists name
      simp
      have h₁ := pop_vals_monotone heq₁ name
      have h₂ := pop_val_monotone heq₂ name
      have h₃ := hpop.2
      subst h₃
      simp [ChanMap.popVal] at heq₂
      split at heq₂; contradiction
      rename_i h₄
      simp at heq₂
      have := heq₂.1
      subst this
      apply h₁
      simp [h₄]

theorem pop_vals_pop_vals_disj_preserves_pairwise
  [DecidableEq χ]
  {map : ChanMap χ V}
  {P : V → V → Prop}
  {names₁ : Vector χ m} {vals₁ : Vector V m}
  {names₂ : Vector χ n} {vals₂ : Vector V n}
  (hpw : map.Pairwise P)
  (hdisj : List.Disjoint names₁.toList names₂.toList)
  (hpop₁ : map.popVals names₁ = some (vals₁, map₁))
  (hpop₂ : map.popVals names₂ = some (vals₂, map₂)) :
    ∀ v₁ v₂, v₁ ∈ vals₁ → v₂ ∈ vals₂ → P v₁ v₂
  := by
  intros v₁ v₂ hmem₁ hmem₂
  have ⟨name₁, hmem_name₁, hmem_v₁⟩ := pop_vals_exists_get_index hpop₁ hmem₁
  have ⟨name₂, hmem_name₂, hmem_v₂⟩ := pop_vals_exists_get_index hpop₂ hmem₂
  replace hmem_name₁ := Vector.mem_toList_iff.mpr hmem_name₁
  replace hmem_name₂ := Vector.mem_toList_iff.mpr hmem_name₂
  have hne : name₁ ≠ name₂ := by
    intros h
    subst h
    exact hdisj hmem_name₁ hmem_name₂
  have ⟨_, hi, hget_v₁⟩ := List.getElem_of_mem hmem_v₁
  have ⟨_, hj, hget_v₂⟩ := List.getElem_of_mem hmem_v₂
  have hpw := hpw (.inl hne) hi hj
  simp [hget_v₁, hget_v₂] at hpw
  exact hpw

end Lemmas

end Wavelet.Dataflow
