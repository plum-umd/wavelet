import Wavelet.Data.List

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

def AsyncOp.EqMod
  (EqV : V → V → Prop) :
    AsyncOp V → AsyncOp V → Prop
  | .switch n₁, .switch n₂ => n₁ = n₂
  | .steer f₁ n₁, .steer f₂ n₂ => f₁ = f₂ ∧ n₁ = n₂
  | .merge s₁ n₁, .merge s₂ n₂ => s₁ = s₂ ∧ n₁ = n₂
  | .forward n₁, .forward n₂ => n₁ = n₂
  | .fork n₁, .fork n₂ => n₁ = n₂
  | .const c₁ n₁, .const c₂ n₂ => EqV c₁ c₂ ∧ n₁ = n₂
  | .forwardc n₁ m₁ consts₁, .forwardc n₂ m₂ consts₂ =>
      n₁ = n₂ ∧ m₁ = m₂ ∧ List.Forall₂ EqV consts₁.toList consts₂.toList
  | .sink n₁, .sink n₂ => n₁ = n₂
  | _, _ => False

def AtomicProc.EqMod
  [Arity Op]
  (EqV : V → V → Prop) : AtomicProc Op χ V → AtomicProc Op χ V → Prop
  | .async aop₁ inputs₁ outputs₁, .async aop₂ inputs₂ outputs₂ =>
    AsyncOp.EqMod EqV aop₁ aop₂ ∧
    inputs₁ = inputs₂ ∧
    outputs₁ = outputs₂
  | .op op₁ inputs₁ outputs₁, .op op₂ inputs₂ outputs₂ =>
    op₁ = op₂ ∧ inputs₁ ≍ inputs₂ ∧ outputs₁ ≍ outputs₂
  | _, _ => False

def Proc.EqMod
  [Arity Op]
  (EqV : V → V → Prop)
  (p₁ p₂ : Proc Op χ V m n) : Prop :=
  p₁.inputs = p₂.inputs ∧
  p₁.outputs = p₂.outputs ∧
  List.Forall₂ (AtomicProc.EqMod EqV) p₁.atoms p₂.atoms

/-- Equal configurations modulo a equivalence relation on values. -/
def Config.EqMod
  [Arity Op] (EqV : V → V → Prop)
  (c₁ c₂ : Config Op χ V m n) : Prop :=
  Proc.EqMod EqV c₁.proc c₂.proc ∧
  ChanMap.EqMod EqV c₁.chans c₂.chans

instance ChanMap.EqMod.instRefl {EqV : V → V → Prop} [IsRefl V EqV] :
  IsRefl (ChanMap χ V) (ChanMap.EqMod EqV) where
  refl map := by
    intros name
    apply List.forall₂_refl

instance ChanMap.EqMod.instSymm {EqV : V → V → Prop} [IsSymm V EqV] :
  IsSymm (ChanMap χ V) (ChanMap.EqMod EqV) where
  symm map₁ map₂ := by
    intros h name
    apply IsSymm.symm _ _ h

instance ChanMap.EqMod.instTrans {EqV : V → V → Prop} [IsTrans V EqV] :
  IsTrans (ChanMap χ V) (ChanMap.EqMod EqV) where
  trans map₁ map₂ map₃ := by
    intros h₁ h₂ name
    apply IsTrans.trans _ _ _ h₁ h₂

instance AsyncOp.EqMod.instRefl {EqV : V → V → Prop} [IsRefl V EqV] :
  IsRefl (AsyncOp V) (AsyncOp.EqMod EqV) where
  refl aop := by cases aop <;> simp [AsyncOp.EqMod, IsRefl.refl]

instance AsyncOp.EqMod.instSymm {EqV : V → V → Prop} [instSymm : IsSymm V EqV] :
  IsSymm (AsyncOp V) (AsyncOp.EqMod EqV) where
  symm aop₁ aop₂ := by
    have := instSymm.symm
    cases aop₁ <;> cases aop₂ <;> simp [AsyncOp.EqMod]
    any_goals grind only [cases Or]
    case forwardc.forwardc =>
      intros h₁ h₂ h₃
      simp [h₁, h₂, IsSymm.symm _ _ h₃]

instance AsyncOp.EqMod.instTrans {EqV : V → V → Prop} [instTrans : IsTrans V EqV] :
  IsTrans (AsyncOp V) (AsyncOp.EqMod EqV) where
  trans aop₁ aop₂ aop₃ := by
    have := instTrans.trans
    cases aop₁ <;> cases aop₂ <;> cases aop₃ <;> simp [AsyncOp.EqMod]
    any_goals grind only [cases Or]
    case forwardc.forwardc =>
      intros h₁ h₂ h₃ h₄ h₅ h₆
      simp [h₁, h₂, h₄, h₅, IsTrans.trans _ _ _ h₃ h₆]

instance AtomicProc.EqMod.instRefl {EqV : V → V → Prop} [Arity Op] [IsRefl V EqV] :
  IsRefl (AtomicProc Op χ V) (AtomicProc.EqMod EqV) where
  refl ap := by cases ap <;> simp [AtomicProc.EqMod, IsRefl.refl]

instance AtomicProc.EqMod.instSymm {EqV : V → V → Prop} [Arity Op] [IsSymm V EqV] :
  IsSymm (AtomicProc Op χ V) (AtomicProc.EqMod EqV) where
  symm ap₁ ap₂ := by
    cases ap₁ <;> cases ap₂ <;> simp [AtomicProc.EqMod]
    any_goals grind only [cases Or]
    case async.async =>
      intros h₁ h₂ h₃
      simp [h₂, h₃, IsSymm.symm _ _ h₁]

instance AtomicProc.EqMod.instTrans {EqV : V → V → Prop} [Arity Op] [IsTrans V EqV] :
  IsTrans (AtomicProc Op χ V) (AtomicProc.EqMod EqV) where
  trans ap₁ ap₂ ap₃ := by
    cases ap₁ <;> cases ap₂ <;> cases ap₃ <;> simp [AtomicProc.EqMod]
    any_goals grind only [cases Or]
    case async.async =>
      intros h₁ h₂ h₃ h₄ h₅ h₆
      simp [h₂, h₃, h₅, h₆, IsTrans.trans _ _ _ h₁ h₄]

instance Proc.EqMod.instRefl {EqV : V → V → Prop} [Arity Op] [IsRefl V EqV] :
  IsRefl (Proc Op χ V m n) (Proc.EqMod EqV) where
  refl p := by cases p; simp [Proc.EqMod, IsRefl.refl]

instance Proc.EqMod.instSymm {EqV : V → V → Prop} [Arity Op] [IsSymm V EqV] :
  IsSymm (Proc Op χ V m n) (Proc.EqMod EqV) where
  symm p₁ p₂ := by
    cases p₁; cases p₂
    simp [Proc.EqMod]
    intros h₁ h₂ h₃
    simp [h₁, h₂, IsSymm.symm _ _ h₃]

instance {EqV : V → V → Prop} [Arity Op] [IsTrans V EqV] :
  IsTrans (Proc Op χ V m n) (Proc.EqMod EqV) where
  trans p₁ p₂ p₃ := by
    cases p₁; cases p₂; cases p₃
    simp [Proc.EqMod]
    intros h₁ h₂ h₃ h₄ h₅ h₆
    simp [h₁, h₂, h₄, h₅, IsTrans.trans _ _ _ h₃ h₆]

instance Config.EqMod.instRefl {EqV : V → V → Prop} [Arity Op] [IsRefl V EqV] :
  IsRefl (Config Op χ V m n) (Config.EqMod EqV) where
  refl c := by cases c; simp [Config.EqMod, IsRefl.refl]

instance Config.EqMod.instSymm {EqV : V → V → Prop} [Arity Op] [IsSymm V EqV] :
  IsSymm (Config Op χ V m n) (Config.EqMod EqV) where
  symm c₁ c₂ := by
    cases c₁
    cases c₂
    simp [Config.EqMod]
    intros h₁ h₂
    simp [IsSymm.symm _ _ h₁]
    exact IsSymm.symm _ _ h₂

instance Config.EqMod.instTrans {EqV : V → V → Prop} [Arity Op] [IsTrans V EqV] :
  IsTrans (Config Op χ V m n) (Config.EqMod EqV) where
  trans c₁ c₂ c₃ := by
    cases c₁
    cases c₂
    cases c₃
    simp [Config.EqMod]
    intros h₁ h₂ h₃ h₄
    simp [IsTrans.trans _ _ _ h₁ h₃]
    exact IsTrans.trans _ _ _ h₂ h₄

@[simp]
theorem AsyncOp.EqMod.eq_eq : AsyncOp.EqMod Eq = Eq (α := AsyncOp V) := by
  funext aop₁ aop₂
  cases aop₁ <;> cases aop₂ <;> simp [EqMod]
  case forwardc.forwardc =>
    intros h₁ h₂
    subst h₁; subst h₂
    simp [Vector.toList_inj]

@[simp]
theorem AtomicProc.EqMod.eq_eq
  [Arity Op] : AtomicProc.EqMod Eq = Eq (α := AtomicProc Op χ V)
  := by
  funext ap₁ ap₂
  simp [EqMod]
  cases ap₁ <;> grind only [EqMod]

@[simp]
theorem Proc.EqMod.eq_eq
  [Arity Op] : Proc.EqMod Eq = Eq (α := Proc Op χ V m n)
  := by
  funext p₁ p₂
  cases p₁
  cases p₂
  simp [EqMod]

@[simp]
theorem Config.EqMod.eq_eq
  [Arity Op] : Config.EqMod Eq = Eq (α := Config Op χ V m n)
  := by
  funext c₁ c₂
  cases c₁
  cases c₂
  simp [EqMod]

theorem chan_map_pop_vals_equiv
  [DecidableEq χ]
  {map₁ map₂ : ChanMap χ V}
  {vals₁ : Vector V k}
  {EqV : V → V → Prop}
  (heq : ChanMap.EqMod EqV map₁ map₂)
  (hpop : map₁.popVals names = some (vals₁, map₁')) :
    ∃ vals₂ map₂',
      map₂.popVals names = some (vals₂, map₂') ∧
      List.Forall₂ EqV vals₁.toList vals₂.toList ∧
      ChanMap.EqMod EqV map₁' map₂'
  := sorry

theorem chan_map_push_vals_equiv
  [DecidableEq χ]
  {map : ChanMap χ V}
  {vals₁ vals₂ : Vector V k}
  {EqV : V → V → Prop}
  (hequiv : List.Forall₂ EqV vals₁.toList vals₂.toList) :
    ChanMap.EqMod EqV
      (map.pushVals names vals₁)
      (map.pushVals names vals₂)
  := sorry

end Wavelet.Dataflow
