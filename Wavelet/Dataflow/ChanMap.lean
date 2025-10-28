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
  ∀ {x₁ x₂}
    {buf₁ buf₂ : List V}
    {i : Fin buf₁.length}
    {j : Fin buf₂.length},
    x₁ ≠ x₂ ∨ i.val ≠ j.val →
    map x₁ = some buf₁ →
    map x₂ = some buf₂ →
    P buf₁[i] buf₂[j]

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
  sorry

/-- If a list of channels already have values ready to pop,
then it can commute with any `pushVals` operation. -/
theorem pop_vals_push_vals_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hpop : chans.popVals vars₂ = some (vals₂, chans')) :
    (chans.pushVals vars₁ outputVals₁).popVals vars₂ =
      some (vals₂, chans'.pushVals vars₁ outputVals₁)
  := sorry

theorem pop_vals_pop_vals_disj_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hdisj : vars₁.toList.Disjoint vars₂.toList)
  (hpop₁ : chans.popVals vars₁ = some (vals₁, chans₁))
  (hpop₂ : chans.popVals vars₂ = some (vals₂, chans₂)) :
    ∃ chans',
      chans₁.popVals vars₂ = some (vals₂, chans') ∧
      chans₂.popVals vars₁ = some (vals₁, chans')
  := sorry

theorem push_vals_push_vals_disj_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hdisj : vars₁.toList.Disjoint vars₂.toList) :
    (chans.pushVals vars₁ vals₁).pushVals vars₂ vals₂
      = (chans.pushVals vars₂ vals₂).pushVals vars₁ vals₁
  := sorry

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
  intros x₁ x₂ buf₁ buf₂ i j hne hget₁ hget₂
  simp [ChanMap.empty] at hget₁
  simp [hget₁] at i
  exact Fin.elim0 i

theorem pop_vals_disj_preserves_pairwise
  [DecidableEq χ]
  {map : ChanMap χ V}
  {P : V → V → Prop}
  {names₁ : Vector χ m} {vals₁ : Vector V m}
  {names₂ : Vector χ n} {vals₂ : Vector V n}
  (hpw : map.Pairwise P)
  (hdisj : List.Disjoint names₁.toList names₂.toList)
  (hpop₁ : map.popVals names₁ = some (vals₁, map'))
  (hpop₂ : map.popVals names₂ = some (vals₂, map'')) :
    ∀ v₁ v₂, v₁ ∈ vals₁ → v₂ ∈ vals₂ → P v₁ v₂
  := sorry

end Lemmas

end Wavelet.Dataflow
