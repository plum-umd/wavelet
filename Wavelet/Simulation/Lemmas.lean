import Batteries.Data.Vector.Lemmas
import Mathlib.Data.List.Nodup

import Wavelet.Dataflow
import Wavelet.Compile

/-! Some lemmas for proving the simulation. -/

namespace Wavelet.Simulation.Lemmas

open Wavelet.Dataflow Wavelet.Compile

variable (χ V)
variable [DecidableEq χ]

theorem push_val_empty
  {map : ChanMap χ V}
  (hempty : map name = []) :
  map.pushVal _ _ name val = λ n => if n = name then [val] else map n := by
  funext name'
  simp [ChanMap.pushVal]
  split
  · rename_i h
    simp [h, hempty]
  · rfl

theorem push_vals_empty
  {map : ChanMap χ V}
  {names : Vector χ n}
  {vals : Vector V n}
  (hnodup : names.toList.Nodup)
  (hempty : ∀ name ∈ names, map name = []) :
  map.pushVals _ _ names vals =
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

theorem pop_val_singleton
  {map : ChanMap χ V}
  (hsingleton : map name = [val]) :
  ∃ map',
    map.popVal _ _ name = some (val, map') ∧
    map' = λ n => if n = name then [] else map n := by
  simp [ChanMap.popVal, hsingleton]

theorem pop_vals_singleton
  {map : ChanMap χ V}
  {names : Vector χ n}
  (prop : χ → V → Prop)
  (hnodup : names.toList.Nodup)
  (hsingletons : ∀ name ∈ names, ∃ val, map name = [val] ∧ prop name val) :
  ∃ map' vals,
    map.popVals _ _ names = some (vals, map') ∧
    map' = (λ n => if n ∈ names then [] else map n) ∧
    List.Forall₂ prop names.toList vals.toList
  := by
  simp [ChanMap.popVals]
  induction n with
  | zero => simp [StateT.run, StateT.pure, Vector.eq_empty, pure]
  | succ n' ih =>
    have : names = names.pop.push names.back := by simp
    rw [this, Vector.mapM_push]
    simp [StateT.run, StateT.bind, Option.bind, bind]
    specialize ih (Vector.nodup_implies_pop_nodup hnodup) _
    · intros name hname
      exact hsingletons name (Vector.mem_pop_implies_mem hname)
    · have ⟨map'', vals', h₁, h₂, h₃⟩ := ih
      simp only [StateT.run] at h₁
      have ⟨val, h₄, h₅⟩ := hsingletons names.back (by simp)
      have h₆ : names.back ∉ names.pop :=
        Vector.nodup_implies_back_not_mem_pop hnodup
      simp [h₁, ChanMap.popVal, h₂, h₄, h₆, pure, StateT.pure]
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

theorem mem_allVarsExcept
  (hmem : name ∈ compileExpr.allVarsExcept χ definedVars vars pathConds) :
  ∃ var,
    name = .var var pathConds ∧
    var ∈ definedVars ∧
    var ∉ vars
:= by
  simp [compileExpr.allVarsExcept] at hmem
  have ⟨var, hvar₁, hvar₂⟩ := hmem
  exists var
  simp [hvar₂]
  simp [List.removeAll, List.toVector] at hvar₁
  exact hvar₁

theorem allVarsExcept_nodup
  (hnodup : definedVars.Nodup) :
  (compileExpr.allVarsExcept χ definedVars vars pathConds).toList.Nodup
:= by
  simp [compileExpr.allVarsExcept, Vector.toList_map]
  apply List.Nodup.map
  simp [Function.Injective]
  apply List.Nodup.filter
  exact hnodup

theorem mem_to_mem_removeAll
  [DecidableEq α]
  {x : α} {l₁ l₂ : List α}
  (h₁ : x ∈ l₁)
  (h₂ : x ∉ l₂) :
  x ∈ (l₁.removeAll l₂)
  := by
  simp [List.removeAll]
  grind

end Wavelet.Simulation.Lemmas
