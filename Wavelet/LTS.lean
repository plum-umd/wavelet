import Wavelet.Op

namespace Wavelet.LTS

open Op

abbrev LTS (C : Type u) (E : Type v) := C → Trace E → C → Prop

inductive LTS.Plus (R : LTS C E) : LTS C E where
  | single : R c tr c' → Plus R c tr c'
  | tail : Plus R c tr c' → R c' tr' c'' → Plus R c (tr ++ tr') c''

inductive LTS.Star (R : LTS C E) : LTS C E where
  | refl : Star R c .ε c
  | tail : Star R c tr c' → R c' tr' c'' → Star R c (tr ++ tr') c''

/-- Simulation of two LTS's. -/
def Simulation
  (c₁ : C₁) (c₂ : C₂)
  (R : C₁ → C₂ → Prop)
  (Step₁ : LTS C₁ E)
  (Step₂ : LTS C₂ E) :=
  R c₁ c₂ ∧
  ∀ c₁ c₂ c₁' tr,
    R c₁ c₂ →
    Step₁ c₁ tr c₁' →
    ∃ c₂',
      Step₂ c₂ tr c₂' ∧
      R c₁' c₂'

def Simulation.base (hsim : Simulation c₁ c₂ R Step₁ Step₂) : R c₁ c₂ := hsim.1

def Simulation.coind (hsim : Simulation c₁ c₂ R Step₁ Step₂) :
  ∀ c₁ c₂ c₁' tr,
    R c₁ c₂ →
    Step₁ c₁ tr c₁' →
    ∃ c₂',
      Step₂ c₂ tr c₂' ∧
      R c₁' c₂' := hsim.2

theorem LTS.step_eq_rhs {R : LTS C E}
  (h : R c₁ tr c₂)
  (heq : c₂ = c₂') :
  R c₁ tr c₂' := by
  simp [heq] at h
  exact h

theorem LTS.step_eq_tr {R : LTS C E}
  (h : R c₁ tr c₂)
  (heq : tr = tr') :
  R c₁ tr' c₂ := by
  simp [heq] at h
  exact h

theorem LTS.step_eq_tr_rhs {R : LTS C E}
  (h : R c₁ tr c₂)
  (heq₁ : tr = tr')
  (heq₂ : c₂ = c₂') :
  R c₁ tr' c₂' := by
  simp [heq₁, heq₂] at h
  exact h

theorem LTS.Star.single
  {R : LTS C E}
  (h : R c₁ tr c₂) :
  LTS.Star R c₁ tr c₂ := .tail (.refl) h

theorem LTS.Star.trans
  {R : LTS C E}
  {c₁ c₂ c₃ : C}
  {tr₁ tr₂ : Trace E}
  (h₁ : LTS.Star R c₁ tr₁ c₂)
  (h₂ : LTS.Star R c₂ tr₂ c₃) :
  LTS.Star R c₁ (tr₁ ++ tr₂) c₃ := by
  induction h₂ with
  | refl => simp [h₁, Trace.ε]
  | tail pre tail ih =>
    rename_i c₂ tr₁ c₃ tr₂ c₄
    have := ih h₁
    apply LTS.step_eq_tr (Star.tail this tail)
    simp

theorem LTS.Plus.trans
  {R : LTS C E}
  {c₁ c₂ c₃ : C}
  {tr₁ tr₂ : Trace E}
  (h₁ : LTS.Plus R c₁ tr₁ c₂)
  (h₂ : LTS.Plus R c₂ tr₂ c₃) :
  LTS.Plus R c₁ (tr₁ ++ tr₂) c₃ := by
  induction h₂ with
  | single tail => exact .tail h₁ tail
  | tail pre tail ih =>
    rename_i c₂ tr₁ c₃ tr₂ c₄
    have := ih h₁
    apply LTS.step_eq_tr (Plus.tail this tail)
    simp

theorem LTS.Plus.to_star
  {R : LTS C E}
  (h : LTS.Plus R c₁ tr c₂) :
  LTS.Star R c₁ tr c₂ := by
  induction h with
  | single h => exact .single h
  | tail _ tail ih => exact .tail ih tail

/-- Defines when an `LTS` is transitive. -/
class LTS.Transitive (R : LTS C E) where
  trans : ∀ {c₁ c₂ c₃ tr₁ tr₂},
    R c₁ tr₁ c₂ →
    R c₂ tr₂ c₃ →
    R c₁ (tr₁ ++ tr₂) c₃

instance {R : LTS C E} : LTS.Transitive (LTS.Star R) where
  trans := by exact LTS.Star.trans

instance {R : LTS C E} : LTS.Transitive (LTS.Plus R) where
  trans := by exact LTS.Plus.trans

end Wavelet.LTS
