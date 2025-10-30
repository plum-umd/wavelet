import Mathlib.Data.List.Nodup
import Wavelet.Data.List

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

/-- Note: this requires the values to be of the same type. -/
def VarMap.disjointUnion
  {V₁ V₂ : Type u}
  (m₁ : VarMap χ₁ V₁)
  (m₂ : VarMap χ₂ V₂) : VarMap (χ₁ ⊕ χ₂) (V₁ ⊕ V₂) :=
  λ v => match v with
  | .inl v₁ => .inl <$> m₁ v₁
  | .inr v₂ => .inr <$> m₂ v₂

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

end Lemmas

end Wavelet.Seq
