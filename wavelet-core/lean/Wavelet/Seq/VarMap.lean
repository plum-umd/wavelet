import Wavelet.Data.Basic

/-! Definition of maps from variables to values. -/

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

end Wavelet.Seq
