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
  | .const c₁ n₁, .const c₂ n₂ => EqV c₁ c₂ ∧ n₁ = n₂
  | .forwardc n₁ m₁ consts₁, .forwardc n₂ m₂ consts₂ =>
      n₁ = n₂ ∧ m₁ = m₂ ∧ List.Forall₂ EqV consts₁.toList consts₂.toList
  | aop₁, aop₂ => aop₁ = aop₂

def AtomicProc.EqMod
  [Arity Op]
  (EqV : V → V → Prop) : AtomicProc Op χ V → AtomicProc Op χ V → Prop
  | .async aop₁ inputs₁ outputs₁, .async aop₂ inputs₂ outputs₂ =>
    AsyncOp.EqMod EqV aop₁ aop₂ ∧
    inputs₁ = inputs₂ ∧
    outputs₁ = outputs₂
  | ap₁, ap₂ => ap₁ = ap₂

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

instance {EqV : V → V → Prop} [IsRefl V EqV] :
  IsRefl (AsyncOp V) (AsyncOp.EqMod EqV) where
  refl := sorry

instance {EqV : V → V → Prop} [IsSymm V EqV] :
  IsSymm (AsyncOp V) (AsyncOp.EqMod EqV) where
  symm := sorry

instance {EqV : V → V → Prop} [IsTrans V EqV] :
  IsTrans (AsyncOp V) (AsyncOp.EqMod EqV) where
  trans := sorry

instance {EqV : V → V → Prop} [Arity Op] [IsRefl V EqV] :
  IsRefl (AtomicProc Op χ V) (AtomicProc.EqMod EqV) where
  refl := sorry

instance {EqV : V → V → Prop} [Arity Op] [IsSymm V EqV] :
  IsSymm (AtomicProc Op χ V) (AtomicProc.EqMod EqV) where
  symm := sorry

instance {EqV : V → V → Prop} [Arity Op] [IsTrans V EqV] :
  IsTrans (AtomicProc Op χ V) (AtomicProc.EqMod EqV) where
  trans := sorry

instance {EqV : V → V → Prop} [Arity Op] [IsRefl V EqV] :
  IsRefl (Proc Op χ V m n) (Proc.EqMod EqV) where
  refl := sorry

instance {EqV : V → V → Prop} [Arity Op] [IsSymm V EqV] :
  IsSymm (Proc Op χ V m n) (Proc.EqMod EqV) where
  symm := sorry

instance {EqV : V → V → Prop} [Arity Op] [IsTrans V EqV] :
  IsTrans (Proc Op χ V m n) (Proc.EqMod EqV) where
  trans := sorry

instance {EqV : V → V → Prop} [Arity Op] [IsRefl V EqV] :
  IsRefl (Config Op χ V m n) (Config.EqMod EqV) where
  refl := sorry

instance {EqV : V → V → Prop} [Arity Op] [IsSymm V EqV] :
  IsSymm (Config Op χ V m n) (Config.EqMod EqV) where
  symm := sorry

instance {EqV : V → V → Prop} [Arity Op] [IsTrans V EqV] :
  IsTrans (Config Op χ V m n) (Config.EqMod EqV) where
  trans := sorry

@[simp]
theorem AsyncOp.EqMod.eq_eq : AsyncOp.EqMod Eq = Eq (α := AsyncOp V) := by
  funext
  simp [EqMod]
  split
  · simp
  · constructor
    · intros h
      have ⟨h₁, h₂, h₃⟩ := h
      subst h₁; subst h₂
      simp [Vector.toList_inj] at h₃
      simp [h₃]
    · intros h
      simp at h
      have ⟨h₁, h₂, h₃⟩ := h
      subst h₁; subst h₂; subst h₃
      simp
  · simp

@[simp]
theorem AtomicProc.EqMod.eq_eq
  [Arity Op] : AtomicProc.EqMod Eq = Eq (α := AtomicProc Op χ V)
  := by
  funext
  simp [EqMod]
  split <;> simp

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
