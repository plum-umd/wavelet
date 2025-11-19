import Wavelet.Seq.VarMap

import Mathlib.Data.List.Nodup
import Wavelet.Thm.Data.List

/-! Lemmas for `ChanMap`. -/

namespace Wavelet.Seq

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
    simp [VarMap.getVar, VarMap.fromList]
    have ⟨i, hi, hget_i⟩ := Vector.mem_iff_getElem.mp hmem_var
    exists vals[i]
    apply Vector.mem_iff_getElem.mpr
    exists i, hi
    simp [hget_i]
  · intros hget_var
    simp [VarMap.getVar, VarMap.fromList] at hget_var
    have ⟨val, var', hfind⟩ := hget_var
    have := List.find?_some hfind
    simp at this
    simp [← this]
    have := List.mem_of_find?_eq_some hfind
    simp at this
    have := Vector.of_mem_zip this
    simp [this.1]

theorem var_map_fromList_get_vars_index
  [DecidableEq χ]
  {vars : Vector χ n} {vals : Vector V n}
  {i : Nat} {hlt : i < n}
  (hnodup : vars.toList.Nodup) :
  (VarMap.fromList (vars.zip vals).toList).getVar vars[i] = some vals[i]
:= by
  simp [VarMap.fromList, VarMap.getVar]
  exists vars[i]
  apply List.find?_eq_some_iff_append.mpr
  constructor
  · simp
  · exists (vars.zip vals).toList.take i
    exists (vars.zip vals).toList.drop (i + 1)
    simp
    constructor
    · have := List.to_append_cons (l := (vars.zip vals).toList) (i := i) (by simp [hlt])
      simp at this
      exact this
    · intros k v hkv
      have ⟨j, hj, hget⟩ := List.mem_take_iff_getElem.mp hkv
      simp at hj
      simp at hget
      simp [←hget.1]
      intros h
      have := (List.Nodup.getElem_inj_iff hnodup).mp h
      simp at this
      omega

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

end Wavelet.Seq
