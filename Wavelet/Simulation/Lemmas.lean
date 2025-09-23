import Batteries.Data.Vector.Lemmas
import Mathlib.Data.List.Nodup

import Wavelet.Dataflow
import Wavelet.Compile

/-! Some lemmas for proving the simulation. -/

namespace Wavelet.Simulation.Lemmas

open Wavelet.Dataflow Wavelet.Compile

variable (χ V)
variable [DecidableEq χ]

theorem push_vals_lookup_diff
  {map : ChanMap χ V}
  (hdiff : ∀ v ∈ names, v ≠ name) :
  map.pushVals _ _ names vals name = map name := sorry

theorem push_vals_lookup_singleton
  {map : ChanMap χ V}
  {names : Vector χ n}
  (i : Fin n)
  (hempty : map names[i] = [])
  (hdisj : names.toList.Nodup)
  (hval : val = vals[i])
  (hname : name = names[i]) :
  map.pushVals _ _ names vals name = [val] := sorry

theorem push_val_lookup_diff
  {map : ChanMap χ V}
  (hdiff : name' ≠ name) :
  map.pushVal _ _ name' val name = map name := sorry

theorem push_val_lookup_singleton
  {map : ChanMap χ V}
  (hempty : map name = []) :
  map.pushVal _ _ name val name = [val] := sorry

theorem pop_vals_lookup_diff
  {map : ChanMap χ V}
  (hpop : map.popVals _ _ names = some (vals, map'))
  (hdiff : ∀ v ∈ names, v ≠ name) :
  map' name = map name := sorry

theorem pop_val_lookup_diff
  {map : ChanMap χ V}
  (hpop : map.popVal _ _ name' = some (val, map'))
  (hdiff : name' ≠ name) :
  map' name = map name := sorry

theorem pop_val_lookup_singleton
  {map : ChanMap χ V}
  (hpop : map.popVal _ _ name = some (val, map'))
  (hsingleton : map name = [val]) :
  map' name = [] := sorry

theorem pop_vals_lookup_singleton
  {map : ChanMap χ V}
  (hpop : map.popVals _ _ names = some (val, map'))
  (hmem : name ∈ names)
  (hsingleton : (map name).length = 1) :
  map' name = [] := sorry

theorem pop_val_singleton
  {map : ChanMap χ V}
  (hsingleton : map name = [val]) :
  ∃ map', map.popVal _ _ name = some (val, map') := by
  simp [ChanMap.popVal, hsingleton]

theorem pop_vals_singleton
  {map : ChanMap χ V}
  {names : Vector χ n}
  (prop : χ → V → Prop)
  (hsingletons : ∀ name ∈ names, ∃ val, map name = [val] ∧ prop name val) :
  ∃ vals map',
    map.popVals _ _ names = some (vals, map') ∧
    List.Forall₂ prop names.toList vals.toList := sorry

theorem push_val_empty_rewrite
  {map : ChanMap χ V}
  (hempty : map name = []) :
  map.pushVal _ _ name val = λ n => if n = name then [val] else map n := by
  funext name'
  simp [ChanMap.pushVal]
  split
  · rename_i h
    simp [h, hempty]
  · rfl

theorem push_vals_empty_rewrite
  {map : ChanMap χ V}
  {names : Vector χ n}
  {vals : Vector V n}
  (hdisj : names.toList.Nodup)
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
    have : names.zip vals = ((names.pop.zip vals.pop)).push (names.zip vals).back
    := by
      simp [Vector.zip_eq_zipWith]
      sorry
    rw [this, Vector.foldl_push]
    sorry

theorem pop_val_singleton_rewrite
  {map : ChanMap χ V}
  (hsingleton : map name = [val]) :
  ∃ map',
    map.popVal _ _ name = some (val, map') ∧
    map' = λ n => if n = name then [] else map n := by
  simp [ChanMap.popVal, hsingleton]

theorem pop_vals_singleton_rewrite
  {map : ChanMap χ V}
  (prop : χ → V → Prop)
  (hdisj : names.toList.Nodup)
  (hsingletons : ∀ name ∈ names, ∃ val, map name = [val] ∧ prop name val) :
  ∃ map' vals,
    map.popVals _ _ names = some (vals, map') ∧
    map' = (λ n => if n ∈ names then [] else map n) ∧
    List.Forall₂ prop names.toList vals.toList := sorry

/-- Popping the same names pushed before -/
theorem pop_vals_singleton_exact
  {map map' : ChanMap χ V}
  (names names' : Vector χ n)
  (vals : Vector V n)
  (hnames : names = names')
  (hmap : ∀ name, map name =
    match names.finIdxOf? name with
    | some i => [vals[i]]
    | none => map' name) :
  ∃ map'',
    map.popVals _ _ names = some (vals, map'') ∧
    map'' = λ n => if n ∈ names then [] else map n := sorry

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
