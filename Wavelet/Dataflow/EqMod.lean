import Wavelet.Dataflow.Proc

namespace Wavelet.Dataflow

open Semantics

/-- Checks if two channel maps are equal modulo an equivalence relation on values. -/
def ChanMap.EqMod
  (Eq : V → V → Prop)
  (map₁ map₂ : ChanMap χ V) : Prop :=
  ∀ {name : χ}, List.Forall₂ Eq (map₁ name) (map₂ name)

instance {Eq : V → V → Prop} [IsRefl V Eq] : IsRefl (ChanMap χ V) (ChanMap.EqMod Eq) where
  refl map := by
    intros name
    apply List.forall₂_refl

@[simp]
theorem ChanMap.EqMod.eq_eq {map₁ map₂ : ChanMap χ V} :
    ChanMap.EqMod Eq map₁ map₂ ↔ map₁ = map₂
  := by
  constructor
  · simp [EqMod]
    intros h
    funext
    apply h
  · intros h
    simp [h, EqMod]

/-- Equal configurations modulo a equivalence relation on values. -/
def Config.EqMod
  [Arity Op] (Eq : V → V → Prop)
  (c₁ c₂ : Config Op χ V m n) : Prop :=
  c₁.proc = c₂.proc ∧
  ChanMap.EqMod Eq c₁.chans c₂.chans

instance {Eq : V → V → Prop} [Arity Op] [IsRefl V Eq] :
  IsRefl (Config Op χ V m n) (Config.EqMod Eq) where
  refl c := by
    constructor
    · rfl
    · apply IsRefl.refl

instance {Eq : V → V → Prop} [Arity Op] [IsSymm V Eq] :
  IsSymm (Config Op χ V m n) (Config.EqMod Eq) where
  symm := sorry

instance {Eq : V → V → Prop} [Arity Op] [IsTrans V Eq] :
  IsTrans (Config Op χ V m n) (Config.EqMod Eq) where
  trans := sorry

@[simp]
theorem Config.EqMod.eq_eq
  [Arity Op] {c₁ c₂ : Config Op χ V m n} :
    Config.EqMod Eq c₁ c₂ ↔ c₁ = c₂
  := by
  simp [EqMod]
  cases c₁; cases c₂
  simp

theorem chan_map_push_vals_equiv
  [DecidableEq χ]
  {map : ChanMap χ V}
  {vals₁ vals₂ : Vector V k}
  {Eq : V → V → Prop}
  (hequiv : List.Forall₂ Eq vals₁.toList vals₂.toList) :
    ChanMap.EqMod EqV
      (ChanMap.pushVals names vals₁ map)
      (ChanMap.pushVals names vals₂ map)
  := sorry

end Wavelet.Dataflow
