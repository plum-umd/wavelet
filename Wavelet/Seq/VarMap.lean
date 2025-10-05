
/-! Definition and lemmas for maps from variables to values. -/

namespace Wavelet.Seq

/-- Partial map from variables. -/
abbrev VarMap χ V := χ → Option V

def VarMap.empty : VarMap χ V := λ _ => none

def VarMap.insertVars
  [DecidableEq χ]
  (vars : Vector χ n)
  (vals : Vector V n)
  (m : VarMap χ V) : VarMap χ V :=
  λ v => ((vars.zip vals).toList.find? (·.1 = v)).map (·.2) <|> m v

def VarMap.getVar (v : χ) (m : VarMap χ V) : Option V := m v

def VarMap.getVars
  (vars : Vector χ n)
  (m : VarMap χ V) : Option (Vector V n) :=
  vars.mapM m

def VarMap.fromList [DecidableEq χ] (kvs : List (χ × V)) : VarMap χ V :=
  λ v => (kvs.find? (·.1 = v)).map (·.2)

def VarMap.removeVar [DecidableEq χ] (v : χ) (m : VarMap χ V) : VarMap χ V :=
  λ v' => if v = v' then none else m v'

def VarMap.removeVars [DecidableEq χ] (vars : List χ) (m : VarMap χ V) : VarMap χ V :=
  λ v => if v ∈ vars then none else m v

/-! Some lemmas about `VarMap`s. -/
section Lemmas

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

end Lemmas

end Wavelet.Seq
