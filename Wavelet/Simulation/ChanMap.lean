import Wavelet.Dataflow

/-! Some lemmas for `ChanMap`s. -/

namespace Wavelet.Simulation.ChanMap

open Wavelet.Dataflow

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
  map.pushVal _ _ name val = λ n => if n = name then [val] else map n := sorry

theorem push_vals_empty_rewrite
  {map : ChanMap χ V}
  {names : Vector χ n}
  {vals : Vector V n}
  (hdisj : names.toList.Nodup)
  (hempty : ∀ name ∈ names, map name = []) :
  map.pushVals _ _ names vals =
    λ n => if let some i := names.finIdxOf? n then [vals[i]]
    else map n := sorry

theorem pop_val_singleton_rewrite
  {map : ChanMap χ V}
  (hsingleton : map name = [val]) :
  ∃ map',
    map.popVal _ _ name = some (val, map') ∧
    map' = λ n => if n = name then [] else map n := sorry

theorem pop_vals_singleton_rewrite
  {map : ChanMap χ V}
  (prop : χ → V → Prop)
  (hdisj : names.toList.Nodup)
  (hsingletons : ∀ name ∈ names, ∃ val, map name = [val] ∧ prop name val) :
  ∃ map' vals,
    map.popVals _ _ names = some (vals, map') ∧
    map' = (λ n => if n ∈ names then [] else map n) ∧
    List.Forall₂ prop names.toList vals.toList := sorry

end Wavelet.Simulation.ChanMap
