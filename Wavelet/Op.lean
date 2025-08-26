import Batteries.Data.List.Basic

/-! Defines the syntax and semantics of operator sets. -/

namespace Wavelet.Op

class PCM (C : Type u) where
  add : C → C → C
  zero : C
  valid : C → Prop
  eq : C → C → Prop

infixl:60 " ⬝ " => PCM.add
infix:50 " ≡ " => PCM.eq
prefix:40 "✓ " => PCM.valid

def PCM.disjoint {C : Type u} [PCM C] (a b : C) : Prop := ✓ a ⬝ b

/-- TODO: Implement some type class for partial order. -/
def PCM.le {C : Type u} [PCM C] (a b : C) : Prop := ∃ c, b ≡ a ⬝ c

def PCM.framePreserving {C : Type u} [PCM C] (a b : C) : Prop :=
  ∀ c, ✓ a ⬝ c → ✓ b ⬝ c

infix:50 " ⊥ " => PCM.disjoint
infix:50 " ≤ " => PCM.le
infix:50 " ⟹ " => PCM.framePreserving

class LawfulPCM (R : Type u) [inst : PCM R] where
  add_comm : ∀ a b : R, a ⬝ b ≡ b ⬝ a
  add_assoc : ∀ a b c : R, (a ⬝ b) ⬝ c ≡ a ⬝ (b ⬝ c)
  add_ident : ∀ a : R, a ⬝ inst.zero ≡ a
  valid_add : ∀ a b : R, ✓ a ⬝ b → ✓ a
  valid_zero : ✓ inst.zero
  valid_eq : ∀ a b : R, a ≡ b → ✓ a → ✓ b
  eq_refl : ∀ a : R, a ≡ a
  eq_symm : ∀ a b : R, a ≡ b → b ≡ a
  eq_trans : ∀ a b c : R, a ≡ b → b ≡ c → a ≡ c

structure OpSpec (T : Type u) (R : Type w) where
  inTys : List T
  outTys : List T
  requires : R
  ensures : R

structure OpSet where
  /-- Base types -/
  T : Type u
  /-- Base values -/
  V : Type v
  /-- Ghost resource algebra -/
  R : Type w
  /-- Operators -/
  Op : Type
  /-- Value types -/
  typeOf : V → T
  /-- Operator specs -/
  specOf : Op → OpSpec T R
  /-- Bool type -/
  isBoolTy : T → Bool
  /-- Convert a type to bool type -/
  asBool : V → Option Bool
  /-- `asBool` behaves correctly -/
  asBool_correct : ∀ v, isBoolTy (typeOf v) ↔ (asBool v).isSome

def OpSet.WellTypedValues (os : OpSet) (ins : List os.V) (inTys : List os.T) : Prop :=
  List.Forall₂ (λ v t => os.typeOf v = t) ins inTys

class OpSemantics (os : OpSet) [PCM os.R] where
  /-- States -/
  S : Type

  /-- TODO: use more general monads? -/
  runOp : os.Op → List os.V → StateT S Option (List os.V)

  /-- Given well-typed inputs and a valid resource, produce well-typed outputs and no additional resource. -/
  op_satisfies_spec (op : os.Op) (s s' : S) (outs : List os.V) (ins : List os.V)
    (hwt_ins : os.WellTypedValues ins (os.specOf op).inTys)
    (hwt_outs : os.WellTypedValues outs (os.specOf op).outTys) :
    (runOp op ins).run s = .some (outs, s') →
    (os.specOf op).requires ⟹ (os.specOf op).ensures

  /- If resource inputs to two operators are disjoint, their interpretations commute. -/
  op_disj_commute (op₁ op₂ : os.Op) (ins₁ ins₂ : List os.V)
    (hwt_ins₁ : os.WellTypedValues ins₁ (os.specOf op₁).inTys)
    (hwt_ins₂ : os.WellTypedValues ins₂ (os.specOf op₂).inTys)
    (hdisj : (os.specOf op₁).requires ⊥ (os.specOf op₂).requires) :
    ∀ (s : S),
      (Prod.mk <$> runOp op₁ ins₁ <*> runOp op₂ ins₂).run s =
      (Prod.mk <$> runOp op₂ ins₂ <*> runOp op₁ ins₁).run s

end Wavelet.Op

namespace Wavelet.L0

open Wavelet.Op

abbrev Var := String
abbrev Vars := List Var
abbrev FnName := String

structure TypedVar (os : OpSet) where
  name : Var
  ty : os.T

abbrev TypedVars os := List (TypedVar os)

inductive Callee (os : OpSet) where
  | op : os.Op → Callee os
  | fn : FnName → Callee os

structure Call (os : OpSet) where
  callee : Callee os
  args : Vars

inductive Binder (os : OpSet) where
  | call : Vars → Call os → Binder os
  | const : Var → os.V → Binder os
  -- | join : Var × Var → Var → Binder os
  -- | split : Var → Var × Var → Binder os

inductive Expr (os : OpSet) where
  | vars : Vars → Expr os
  | tail : Call os → Expr os
  | bind : Binder os → Expr os → Expr os
  | branch : Var → Expr os → Expr os → Expr os

structure FnDef (os : OpSet) where
  name : FnName
  ins : TypedVars os
  outTys : List os.T
  requires : os.R
  ensures : os.R
  body : Expr os

abbrev FnCtx os := List (FnDef os)
abbrev VarCtx (os : OpSet) := Var → Option (os.T)
abbrev ResCtx (os : OpSet) := os.R

structure Ctx (os : OpSet) where
  fns : FnCtx os
  vars : VarCtx os
  res : ResCtx os

def FnCtx.intersect {os : OpSet} (fns₁ fns₂ : FnCtx os) : FnCtx os :=
  fns₁.filter (λ fn₁ => fns₂.any (λ fn₂ => fn₁.name = fn₂.name))

def VarCtx.get (vars : VarCtx os) (x : Var) : Option os.T := vars x

def VarCtx.insert (vars : VarCtx os) (x : Var) (t : os.T) : VarCtx os :=
  λ y => if y = x then some t else vars y

def VarCtx.insertTypedVars (vars : VarCtx os) (vs : TypedVars os) : VarCtx os :=
  vs.foldl (λ ctx v => ctx.insert v.name v.ty) vars

def VarCtx.fromTypedVars (vs : TypedVars os) : VarCtx os :=
  λ x => TypedVar.ty <$> vs.find? (λ v => v.name = x)

def Ctx.WellTypedVars {os : OpSet} (Γ : Ctx os) (vs : Vars) (tys : List os.T) : Prop :=
  List.Forall₂ (λ v t => Γ.vars.get v = some t) vs tys

def Ctx.getFn {os : OpSet} (Γ : Ctx os) (f : FnName) : Option (FnDef os) :=
  Γ.fns.find? (λ fn => fn.name = f)

def Ctx.removeFn {os : OpSet} (Γ : Ctx os) (f : FnName) : Ctx os :=
  { Γ with fns := Γ.fns.filter (λ fn => fn.name ≠ f) }

inductive Call.WellTyped {os : OpSet} [PCM os.R] : Ctx os → Call os → Ctx os → List os.T → Prop where
  /-- Well-typed operator call -/
  | wt_call_op {args} :
    Γ.WellTypedVars args (os.specOf op).inTys →
    (os.specOf op).requires ⬝ frame = Γ.res →
    Call.WellTyped
      Γ { callee := .op op, args := args }
      { Γ with res := (os.specOf op).ensures ⬝ frame } (os.specOf op).outTys
  /-- Well-typed function call -/
  | wt_call_fn {args} :
    Γ.getFn f = some fn →
    Γ.WellTypedVars args (TypedVar.ty <$> fn.ins) →
    fn.requires ⬝ frame = Γ.res →
    Call.WellTyped
      Γ { callee := .fn f, args := args }
      { Γ.removeFn f with res := fn.ensures ⬝ frame } fn.outTys

inductive Expr.WellTyped {os : OpSet} [PCM os.R] : Ctx os → Expr os → Ctx os → List os.T → Prop where
  /-- Well-typed variables -/
  | wt_vars :
    Γ.WellTypedVars vs tys →
    Expr.WellTyped Γ (.vars vs) Γ tys
  /-- Well-typed tail call -/
  | wt_tail {Γ' tys} :
    Call.WellTyped Γ c Γ' tys →
    Expr.WellTyped Γ (.tail c) Γ' tys
  /-- Well-typed branching -/
  | wt_branch :
    Γ.vars.get x = some t →
    os.isBoolTy t →
    Expr.WellTyped Γ left Γ₁ tys →
    Expr.WellTyped Γ right Γ₂ tys →
    Γ.vars x = some t →
    res' ≤ Γ₁.res →
    res' ≤ Γ₂.res →
    Expr.WellTyped
      Γ (.branch x left right)
      {
        fns := Γ₁.fns.intersect Γ₂.fns,
        vars := Γ.vars, -- TODO: not used?
        res := res'
      } tys

def FnDef.WellTyped {os : OpSet} [PCM os.R] (fns fns' : FnCtx os) (fn : FnDef os) : Prop :=
  ∃ vars' res',
    Expr.WellTyped
      { fns, vars := VarCtx.fromTypedVars fn.ins, res := fn.requires }
      fn.body
      { fns := fns', vars := vars', res := res' }
      fn.outTys ∧
    res' ≤ fn.ensures

inductive FnCtx.WellTyped {os : OpSet} [PCM os.R] : FnCtx os → Prop where
  | wt_fn_ctx_nil : FnCtx.WellTyped []
  | wt_fn_ctx_cons {fns' fn} :
    FnCtx.WellTyped fns' →
    FnDef.WellTyped fns fns' fn →
    FnCtx.WellTyped (.cons fn fns)

end Wavelet.L0
