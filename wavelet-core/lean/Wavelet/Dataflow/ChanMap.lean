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

/-- A custom property satisfied by any non-empty channel -/
def ChanMap.AllNames (P : χ → Prop) (map : ChanMap χ V) : Prop :=
  ∀ {name}, map name ≠ [] → P name

@[simp]
abbrev ChanMap.PairwiseWithVals
  (P : V → V → Prop)
  (vals : Vector V n)
  (map : ChanMap χ V) : Prop :=
  ∀ {name val₁ val₂},
    val₁ ∈ map name →
    val₂ ∈ vals →
    P val₁ val₂

end Wavelet.Dataflow
