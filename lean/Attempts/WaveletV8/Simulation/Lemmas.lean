import Batteries.Data.Vector.Lemmas
import Mathlib.Data.List.Nodup

import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

/-! Some lemmas for proving the simulation. -/

namespace Wavelet.Simulation.Lemmas

open Wavelet.Op Wavelet.Seq Wavelet.Dataflow Wavelet.Compile

/-! Lemmas about `ChanMap`. -/
section ChanMap

variable (χ V)
variable [DecidableEq χ]

theorem push_val_empty
  {map : ChanMap χ V}
  (hempty : map name = []) :
  map.pushVal name val = λ n => if n = name then [val] else map n := by
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

theorem pop_val_singleton
  {map : ChanMap χ V}
  (hsingleton : map name = [val]) :
  ∃ map',
    map.popVal name = some (val, map') ∧
    map' = λ n => if n = name then [] else map n := by
  simp [ChanMap.popVal, hsingleton]

theorem pop_vals_singleton
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

end ChanMap

/-! Some lemmas about `VarMap`s. -/
section VarMap

theorem var_map_fromList_get_vars
  [DecidableEq χ]
  {var : χ} {vars : Vector χ n} {vals : Vector V n} :
  var ∈ vars ↔
  ∃ val, (VarMap.fromList (vars.zip vals).toList).getVar var = some val
:= by
  constructor
  · intros hmem_var
    suffices h :
      ((VarMap.fromList (vars.zip vals).toList).getVar var).isSome by
      exact Option.isSome_iff_exists.mp h
    simp [VarMap.getVar, VarMap.fromList,
      Vector.zip_eq_zipWith,
      Vector.toList_zipWith,
      ← List.zip_eq_zipWith]
    sorry
  · intros hget_var
    sorry

theorem var_map_fromList_get_vars_index
  [DecidableEq χ]
  {vars : Vector χ n} {vals : Vector V n}
  {i : Nat} {hlt : i < n}
  (hnodup : vars.toList.Nodup) :
  (VarMap.fromList (vars.zip vals).toList).getVar vars[i] = some vals[i]
:= sorry

theorem var_map_insert_vars_disj
  [DecidableEq χ]
  {map : VarMap χ V}
  (hnot_mem : var ∉ vars) :
  (map.insertVars vars vals).getVar var
  = map.getVar var
:= by
  simp [VarMap.getVar, VarMap.insertVars]
  suffices h :
    List.find? (fun x => decide (x.fst = var)) (vars.zip vals).toList = none
    by simp [h]
  simp
  intros a b h h'
  have := Vector.of_mem_zip h
  simp [h'] at this
  simp [hnot_mem this.1]

theorem var_map_remove_vars_disj
  [DecidableEq χ]
  {map : VarMap χ V}
  (hnot_mem : var ∉ vars) :
  (map.removeVars vars).getVar var
  = map.getVar var
:= by
  simp [VarMap.getVar, VarMap.removeVars]
  intros h
  exfalso
  exact hnot_mem h

end VarMap

/-! Lemmas about various `compileExpr` components. -/
section Compile

theorem mem_allVarsExcept
  [DecidableEq χ]
  {definedVars : List χ}
  (hmem : name ∈ compileExpr.allVarsExcept definedVars vars pathConds) :
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
  [DecidableEq χ]
  {definedVars : List χ}
  (hnodup : definedVars.Nodup) :
  (compileExpr.allVarsExcept definedVars vars pathConds).toList.Nodup
:= by
  simp [compileExpr.allVarsExcept, Vector.toList_map]
  apply List.Nodup.map
  simp [Function.Injective]
  apply List.Nodup.filter
  exact hnodup

theorem allVarsExcept_finIdxOf?_none_if_removed
  [DecidableEq χ]
  {definedVars : List χ}
  (hmem_var : var ∈ removedVars) :
  (compileExpr.allVarsExcept definedVars removedVars pathConds).finIdxOf?
    (.var var pathConds') = none
:= by
  simp [compileExpr.allVarsExcept, List.removeAll]
  intros hmem
  simp [List.toVector] at hmem
  exact False.elim (hmem.2 hmem_var)

theorem allVarsExcept_finIdxOf?_none_if_not_defined
  [DecidableEq χ]
  {definedVars : List χ}
  (hnot_mem_var : var ∉ definedVars) :
  (compileExpr.allVarsExcept definedVars removedVars pathConds).finIdxOf?
    (.var var pathConds') = none
:= by
  sorry

theorem allVarsExcept_finIdxOf?_none_if_diff_path_conds
  [DecidableEq χ]
  {definedVars : List χ}
  (hneq : pathConds ≠ pathConds') :
  (compileExpr.allVarsExcept definedVars removedVars pathConds).finIdxOf?
    (.var var pathConds') = none
:= by
  sorry

theorem allVarsExcept_finIdxOf?_some
  [DecidableEq χ]
  {definedVars : List χ}
  (h₁ : var ∈ definedVars)
  (h₂ : var ∉ removedVars)
  (h₃ : pathConds' = pathConds) :
  ∃ i,
    (compileExpr.allVarsExcept definedVars removedVars pathConds).finIdxOf?
      (.var var pathConds') = some i
:= by
  sorry

theorem vars_nodup_to_var_names_nodup
  {vars : Vector χ n}
  (hnodup : vars.toList.Nodup) :
  (vars.map (ChanName.var · pathConds)).toList.Nodup
:= by
  simp only [Vector.toList_map]
  apply List.Nodup.map _ hnodup
  simp [Function.Injective]

theorem exprOutputs_nodup :
  (compileExpr.exprOutputs m n pathConds).toList.Nodup
:= by
  simp only [
    compileExpr.exprOutputs, Vector.toList_append, Vector.toList_push,
    Vector.toList_map, Vector.toList_range]
  apply List.Nodup.append
  · apply List.Nodup.map _ List.nodup_range
    simp [Function.Injective]
  · apply List.Nodup.append
    · apply List.Nodup.map _ List.nodup_range
      simp [Function.Injective]
    · simp
    · simp
  · simp
    apply List.disjoint_iff_ne.mpr
    simp

theorem tailExprOutputs_nodup :
  (compileExpr.tailExprOutputs m n pathConds).toList.Nodup
:= by
  simp only [
    compileExpr.tailExprOutputs, Vector.toList_append, Vector.toList_push,
    Vector.toList_map, Vector.toList_range]
  apply List.Nodup.append
  · apply List.Nodup.map _ List.nodup_range
    simp [Function.Injective]
  · apply List.Nodup.append
    · apply List.Nodup.map _ List.nodup_range
      simp [Function.Injective]
    · simp
    · simp
  · simp
    apply List.disjoint_iff_ne.mpr
    simp

theorem tailExprOutputs_finIdxOf?_none_to_exprOutputs
  [DecidableEq χ]
  {name : ChanName χ} :
  (compileExpr.tailExprOutputs m n pathConds).finIdxOf? name = none →
  (compileExpr.exprOutputs m n pathConds).finIdxOf? name = none
:= sorry

/-- Converts indices found in `tailExprOutputs` to those in `exprOutputs` -/
theorem tailExprOutputs_finIdxOf?_some_to_exprOutputs
  [DecidableEq χ]
  {name : ChanName χ}
  (h : (compileExpr.tailExprOutputs m n pathConds).finIdxOf? name = some i) :
  (compileExpr.exprOutputs m n pathConds).finIdxOf? name = some (
    if _ : i < m then ⟨n + i, by omega⟩
    else if i < n + m then ⟨i - m, by omega⟩
    else ⟨n + m, by omega⟩
  )
:= sorry

theorem exprOutputs_finIdxOf?_tail_cond
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.tail_cond pathConds) = some (⟨n + m, by simp⟩)
  := by
  simp only [compileExpr.exprOutputs]
  apply Vector.finIdxOf?_eq_some_iff.mpr
  constructor
  · simp [Vector.get_eq_getElem]
  · intros j hj hget
    simp [Vector.get_eq_getElem, Vector.getElem_append] at hget
    split at hget
    · simp at hget
    · simp [Vector.getElem_push] at hget
      omega

theorem exprOutputs_finIdxOf?_tail_args
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)}
  (hi : i < m) :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.tail_arg i pathConds) = some (⟨n + i, by omega⟩)
  := by
  simp [compileExpr.exprOutputs]
  constructor
  · simp [Vector.get_eq_getElem, hi]
  · intros j hj hget
    simp [Vector.get_eq_getElem, Vector.getElem_append] at hget
    split at hget <;> rename_i h
    · simp at hget
    · simp [Vector.getElem_push] at hget
      split at hget
      · simp [Fin.lt_def] at hj
        simp at hget
        omega
      · simp at hget

theorem exprOutputs_finIdxOf?_dest
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)}
  (hi : i < n) :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.dest i pathConds) = some (⟨i, by omega⟩)
  := by
  simp [compileExpr.exprOutputs]
  constructor
  · simp [Vector.get_eq_getElem, hi]
  · intros j hj hget
    simp [Vector.get_eq_getElem, Vector.getElem_append] at hget
    split at hget <;> rename_i h
    · simp [Fin.lt_def] at hj
      simp at hget
      omega
    · simp [Vector.getElem_push] at hget
      split at hget
      · simp [Fin.lt_def] at hj
        simp at hget
      · simp at hget

theorem exprOutputs_finIdxOf?_no_match_dest
  [DecidableEq χ]
  {pathConds pathConds' : List (Bool × ChanName χ)}
  (hi : i < n → pathConds' ≠ pathConds) :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.dest i pathConds') = none
  := by
  if h : i < n then
    simp [compileExpr.exprOutputs, Ne.symm (hi h)]
  else
    simp [compileExpr.exprOutputs, h]

theorem exprOutputs_finIdxOf?_no_match_tail_args
  [DecidableEq χ]
  {pathConds pathConds' : List (Bool × ChanName χ)}
  (hi : i < m → pathConds' ≠ pathConds) :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.tail_arg i pathConds') = none
  := by
  if h : i < m then
    simp [compileExpr.exprOutputs, Ne.symm (hi h)]
  else
    simp [compileExpr.exprOutputs, h]

theorem exprOutputs_finIdxOf?_no_match_tail_cond
  [DecidableEq χ]
  {pathConds pathConds' : List (Bool × ChanName χ)}
  (h : pathConds' ≠ pathConds) :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.tail_cond pathConds') = none
  := by simp [compileExpr.exprOutputs, h]

@[simp]
theorem exprOutputs_finIdxOf?_no_match_var
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.var v pathConds') = none
  := by simp [compileExpr.exprOutputs]

@[simp]
theorem tailExprOutputs_finIdxOf?_no_match_var
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.tailExprOutputs m n pathConds).finIdxOf?
    (.var v pathConds') = none
  := by simp [compileExpr.tailExprOutputs]

@[simp]
theorem exprOutputs_finIdxOf?_no_match_merge_cond
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.merge_cond condName) = none
  := by simp [compileExpr.exprOutputs]

@[simp]
theorem exprOutputs_finIdxOf?_no_match_tail_cond_carry
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    .tail_cond_carry = none
  := by simp [compileExpr.exprOutputs]

@[simp]
theorem exprOutputs_finIdxOf?_no_match_tail_cond_steer_dests
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    .tail_cond_steer_dests = none
  := by simp [compileExpr.exprOutputs]

@[simp]
theorem exprOutputs_finIdxOf?_no_match_tail_cond_steer_tail_args
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    .tail_cond_steer_tail_args = none
  := by simp [compileExpr.exprOutputs]

@[simp]
theorem exprOutputs_finIdxOf?_no_match_final_dest
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.final_dest i) = none
  := by simp [compileExpr.exprOutputs]

@[simp]
theorem exprOutputs_finIdxOf?_no_match_final_tail_arg
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.final_tail_arg i) = none
  := by simp [compileExpr.exprOutputs]

@[simp]
theorem exprOutputs_finIdxOf?_no_match_input
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.input i) = none
  := by simp [compileExpr.exprOutputs]

@[simp]
theorem exprOutputs_finIdxOf?_no_match_switch_cond
  [DecidableEq χ]
  {pathConds : List (Bool × ChanName χ)} :
  (compileExpr.exprOutputs m n pathConds).finIdxOf?
    (.switch_cond i) = none
  := by simp [compileExpr.exprOutputs]

theorem path_conds_nodup_alt
  (hnodup : (pathConds.map Prod.snd).Nodup)
  (hpath_conds : ((b, condName) :: tailConds).Sublist pathConds) :
  (b', condName) ∉ tailConds := by grind

theorem input_finIdxOf?_index
  [DecidableEq χ]
  {vars : Vector χ n} {i : Nat} {hlt : i < n}
  (hnodup : vars.toList.Nodup) :
  (Vector.map ChanName.input vars).finIdxOf? (ChanName.input vars[i])
  = some (⟨i, by omega⟩)
:= by
  apply Vector.finIdxOf?_eq_some_iff.mpr
  simp [Vector.get]
  intros j hj hget
  have := (List.Nodup.get_inj_iff hnodup).mp hget
  simp at this
  simp [← this] at hj

end Compile

end Wavelet.Simulation.Lemmas
