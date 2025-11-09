import Batteries.Data.Vector.Lemmas
import Mathlib.Data.List.Nodup

import Wavelet.Compile.Fn.Defs

/-! Lemmas about various components of `compileFn`. -/

namespace Wavelet.Compile

open Semantics Seq Dataflow

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
  simp [compileExpr.allVarsExcept, List.removeAll]
  simp [List.toVector]
  intros hmem
  exact False.elim (hnot_mem_var hmem)

theorem allVarsExcept_finIdxOf?_none_if_diff_path_conds
  [DecidableEq χ]
  {definedVars : List χ}
  (hneq : pathConds ≠ pathConds') :
  (compileExpr.allVarsExcept definedVars removedVars pathConds).finIdxOf?
    (.var var pathConds') = none
:= by
  simp [compileExpr.allVarsExcept]
  intros hmem
  exact hneq

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
  apply Option.isSome_iff_exists.mp
  simp [compileExpr.allVarsExcept, h₃, List.removeAll]
  simp [List.toVector]
  constructor <;> assumption

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
:= by
  intros hnone
  simp [compileExpr.tailExprOutputs, compileExpr.exprOutputs] at hnone ⊢
  have ⟨h₁, h₂, h₃⟩ := hnone
  and_intros <;> assumption

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
:= by
  cases h₁ : name with
  | tail_arg =>
    simp [compileExpr.tailExprOutputs, h₁, Vector.get,
      Array.getElem_append, Array.getElem_push] at h
    split at h <;> rename_i h₂
    · simp at h
      simp [compileExpr.exprOutputs, h₂, Vector.get,
        Array.getElem_append, Array.getElem_push]
      simp [h.1]
      intros j hj hget
      split_ifs at hget
      rename_i h₃ _
      simp at hget h₃
      simp [h₃, ← hget] at hj
    · split at h <;> simp at h
  | dest =>
    simp [compileExpr.tailExprOutputs, h₁, Vector.get,
      Array.getElem_append, Array.getElem_push] at h
    split at h <;> rename_i h₂
    · simp at h
    · split at h <;> rename_i h₃
      · simp [compileExpr.exprOutputs, h₂, Vector.get,
          Array.getElem_append, Array.getElem_push]
        simp at h
        have h₄ : ↑i < n + m := by omega
        simp [h₄, h₃]
        constructor
        · simp at h₂
          exact h.1
        · intros j hj hget
          split_ifs at hget
          simp at hget
          simp [← h.1] at hget
          simp [← hget] at hj
      · simp at h
  | tail_cond =>
    simp [compileExpr.tailExprOutputs, h₁, Vector.get,
      Array.getElem_append, Array.getElem_push] at h
    split at h <;> rename_i h₂
    · simp at h
    · split at h <;> rename_i h₃
      · simp at h
      · simp at h
        have h₄ : ¬(↑i < n + m) := by omega
        simp [compileExpr.exprOutputs, h₂, h₄, h, Vector.get,
          Array.getElem_append, Array.getElem_push]
        intros j hj hget
        split_ifs at hget
        omega
  | _ =>
    have : (compileExpr.tailExprOutputs m n pathConds).finIdxOf? name = none := by
      simp [compileExpr.tailExprOutputs, h₁]
    simp [this] at h

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

theorem input_finIdxOf?_none
  [DecidableEq χ]
  {vars : Vector χ n}
  (hnot_mem : var ∉ vars) :
  (Vector.map ChanName.input vars).finIdxOf? (ChanName.input var) = none
:= by
  apply Vector.finIdxOf?_eq_none_iff.mpr
  simp [hnot_mem]

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

theorem final_dest_finIdxOf?_index
  [DecidableEq χ]
  {i : Nat}
  (hlt : i < n) :
  ((Vector.range n).map ChanName.final_dest).finIdxOf?
    (ChanName.final_dest (χ := χ) i)
    = some (⟨i, by omega⟩)
  := by
  apply Vector.finIdxOf?_eq_some_iff.mpr
  simp [Vector.get]
  intros j hj hget
  simp [← hget] at hj

theorem final_dest_finIdxOf?_none
  [DecidableEq χ]
  {i : Nat}
  (hlt : i ≥ n) :
  ((Vector.range n).map ChanName.final_dest).finIdxOf?
    (ChanName.final_dest (χ := χ) i) = none
  := by
  apply Vector.finIdxOf?_eq_none_iff.mpr
  simp [hlt]

end Wavelet.Compile
