import Batteries.Data.List.Basic

/-! A formulation of partial commutative monoids. -/
namespace Wavelet.PCM

/-
██████╗  ██████╗███╗   ███╗     █████╗ ██╗  ██╗██╗ ██████╗ ███╗   ███╗███████╗
██╔══██╗██╔════╝████╗ ████║    ██╔══██╗╚██╗██╔╝██║██╔═══██╗████╗ ████║██╔════╝
██████╔╝██║     ██╔████╔██║    ███████║ ╚███╔╝ ██║██║   ██║██╔████╔██║███████╗
██╔═══╝ ██║     ██║╚██╔╝██║    ██╔══██║ ██╔██╗ ██║██║   ██║██║╚██╔╝██║╚════██║
██║     ╚██████╗██║ ╚═╝ ██║    ██║  ██║██╔╝ ██╗██║╚██████╔╝██║ ╚═╝ ██║███████║
╚═╝      ╚═════╝╚═╝     ╚═╝    ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝ ╚═════╝ ╚═╝     ╚═╝╚══════╝
-/

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

end Wavelet.PCM

/-! Semantics of operators that our source and target languages are parametric in. -/
namespace Wavelet.Op

open Wavelet.PCM

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
  /-- Ghost resource types -/
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

/-! Syntax and typing rules of L0, a first-order sequential language with affine resources. -/
namespace Wavelet.L0

open Wavelet.Op Wavelet.PCM

/-
███████╗██╗   ██╗███╗   ██╗████████╗ █████╗ ██╗  ██╗
██╔════╝╚██╗ ██╔╝████╗  ██║╚══██╔══╝██╔══██╗╚██╗██╔╝
███████╗ ╚████╔╝ ██╔██╗ ██║   ██║   ███████║ ╚███╔╝
╚════██║  ╚██╔╝  ██║╚██╗██║   ██║   ██╔══██║ ██╔██╗
███████║   ██║   ██║ ╚████║   ██║   ██║  ██║██╔╝ ██╗
╚══════╝   ╚═╝   ╚═╝  ╚═══╝   ╚═╝   ╚═╝  ╚═╝╚═╝  ╚═╝
-/

abbrev Var := String
abbrev Vars := List Var
abbrev FnName := String

structure TypedVar (T : Type u) where
  name : Var
  ty : T

abbrev TypedVars (T : Type u) := List (TypedVar T)

def TypedVars.fromLists {os : OpSet}
  (vars : List Var) (tys : List os.T) : Option (TypedVars os.T) :=
  if vars.length = tys.length then
    some ((vars.zip tys).map (λ (v, t) => TypedVar.mk v t))
  else
    none

inductive Callee (os : OpSet) where
  | op : os.Op → Callee os
  | fn : FnName → Callee os

structure Call (os : OpSet) where
  callee : Callee os
  args : Vars

inductive Binder (os : OpSet) where
  | call : Vars → Call os → Binder os
  | const : Var → os.V → Binder os

inductive Expr (os : OpSet) where
  | vars : Vars → Expr os
  | tail : Call os → Expr os
  | bind : Binder os → Expr os → Expr os
  | branch : Var → Expr os → Expr os → Expr os

structure FnDef (os : OpSet) where
  name : FnName
  ins : TypedVars os.T
  outTys : List os.T
  requires : os.R
  ensures : os.R
  body : Expr os

/-
████████╗██╗   ██╗██████╗ ██╗███╗   ██╗ ██████╗      ██████╗ ██████╗ ███╗   ██╗████████╗███████╗██╗  ██╗████████╗
╚══██╔══╝╚██╗ ██╔╝██╔══██╗██║████╗  ██║██╔════╝     ██╔════╝██╔═══██╗████╗  ██║╚══██╔══╝██╔════╝╚██╗██╔╝╚══██╔══╝
   ██║    ╚████╔╝ ██████╔╝██║██╔██╗ ██║██║  ███╗    ██║     ██║   ██║██╔██╗ ██║   ██║   █████╗   ╚███╔╝    ██║
   ██║     ╚██╔╝  ██╔═══╝ ██║██║╚██╗██║██║   ██║    ██║     ██║   ██║██║╚██╗██║   ██║   ██╔══╝   ██╔██╗    ██║
   ██║      ██║   ██║     ██║██║ ╚████║╚██████╔╝    ╚██████╗╚██████╔╝██║ ╚████║   ██║   ███████╗██╔╝ ██╗   ██║
   ╚═╝      ╚═╝   ╚═╝     ╚═╝╚═╝  ╚═══╝ ╚═════╝      ╚═════╝ ╚═════╝ ╚═╝  ╚═══╝   ╚═╝   ╚══════╝╚═╝  ╚═╝   ╚═╝
-/

/-- Variable context as a function for convenience -/
abbrev VarCtx (T : Type u) := Var → Option T

def VarCtx.get (vars : VarCtx T) (x : Var) : Option T := vars x

def VarCtx.insert (vars : VarCtx T) (x : Var) (t : T) : VarCtx T :=
  λ y => if y = x then some t else vars y

def VarCtx.remove (vars : VarCtx T) (x : Var) : VarCtx T :=
  λ y => if y = x then none else vars y

def VarCtx.insertTypedVars (vars : VarCtx T) (vs : TypedVars T) : VarCtx T :=
  vs.foldl (λ ctx v => ctx.insert v.name v.ty) vars

def VarCtx.fromTypedVars (vs : TypedVars T) : VarCtx T :=
  λ x => TypedVar.ty <$> vs.find? (λ v => v.name = x)

/--
For convenience, new `FnDef`s are inserted at the front,
i.e., `FnDef`s at the front can only call those at the back.
-/
abbrev FnCtx os := List (FnDef os)

structure Ctx (os : OpSet) where
  self : FnDef os
  fns : FnCtx os
  vars : VarCtx os.T
  res : os.R

def FnCtx.intersect {os : OpSet} (fns₁ fns₂ : FnCtx os) : FnCtx os :=
  fns₁.filter (λ fn₁ => fns₂.any (λ fn₂ => fn₁.name = fn₂.name))

def Ctx.WellTypedVars {os : OpSet} (Γ : Ctx os) (vs : Vars) (tys : List os.T) : Prop :=
  List.Forall₂ (λ v t => Γ.vars.get v = some t) vs tys

def Ctx.getFn {os : OpSet} (Γ : Ctx os) (f : FnName) : Option (FnDef os) :=
  Γ.fns.find? (λ fn => fn.name = f)

def Ctx.updateRes {os : OpSet} (Γ : Ctx os) (r : os.R) : Ctx os :=
  { Γ with res := r }

/-
████████╗██╗   ██╗██████╗ ██╗███╗   ██╗ ██████╗     ██████╗ ██╗   ██╗██╗     ███████╗███████╗
╚══██╔══╝╚██╗ ██╔╝██╔══██╗██║████╗  ██║██╔════╝     ██╔══██╗██║   ██║██║     ██╔════╝██╔════╝
   ██║    ╚████╔╝ ██████╔╝██║██╔██╗ ██║██║  ███╗    ██████╔╝██║   ██║██║     █████╗  ███████╗
   ██║     ╚██╔╝  ██╔═══╝ ██║██║╚██╗██║██║   ██║    ██╔══██╗██║   ██║██║     ██╔══╝  ╚════██║
   ██║      ██║   ██║     ██║██║ ╚████║╚██████╔╝    ██║  ██║╚██████╔╝███████╗███████╗███████║
   ╚═╝      ╚═╝   ╚═╝     ╚═╝╚═╝  ╚═══╝ ╚═════╝     ╚═╝  ╚═╝ ╚═════╝ ╚══════╝╚══════╝╚══════╝
-/

inductive Call.WellTyped {os : OpSet} [PCM os.R] : Ctx os → Call os → Ctx os → List os.T → Prop where
  /-- Well-typed operator call -/
  | wt_call_op {args} :
    Γ.WellTypedVars args (os.specOf op).inTys →
    (os.specOf op).requires ⬝ frame = Γ.res →
    Call.WellTyped
      Γ { callee := .op op, args := args }
      { Γ with res := (os.specOf op).ensures ⬝ frame }
      (os.specOf op).outTys
  /-- Well-typed function call -/
  | wt_call_fn {args} :
    Γ.getFn f = some fn →
    Γ.WellTypedVars args (TypedVar.ty <$> fn.ins) →
    fn.requires ⬝ frame = Γ.res →
    Call.WellTyped
      Γ { callee := .fn f, args := args }
      { Γ with res := fn.ensures ⬝ frame }
      fn.outTys

inductive Binder.WellTyped {os : OpSet} [PCM os.R] : Ctx os → Binder os → Ctx os → Prop where
  /-- Well-typed call -/
  | wt_bind_call {call} :
    Call.WellTyped Γ call Γ' tys →
    TypedVars.fromLists vars tys = some typedVars →
    Binder.WellTyped Γ (.call vars call)
      { Γ with vars := Γ.vars.insertTypedVars typedVars }
  /-- Well-typed constant binder -/
  | wt_bind_const :
    Binder.WellTyped Γ (.const var val)
      { Γ with vars := Γ.vars.insert var (os.typeOf val) }

inductive Expr.WellTyped {os : OpSet} [PCM os.R] : Ctx os → Expr os → Ctx os → List os.T → Prop where
  /-- Well-typed variables -/
  | wt_vars :
    Γ.WellTypedVars vs tys →
    Expr.WellTyped Γ (.vars vs) Γ tys
  /-- Well-typed tail call -/
  | wt_tail {Γ' tys} :
    Call.WellTyped Γ c Γ' tys →
    Expr.WellTyped Γ (.tail c) Γ' tys
  /-- Well-typed recursive tail call -/
  | wt_tail_rec :
    Γ.WellTypedVars args (TypedVar.ty <$> Γ.self.ins) →
    Γ.self.requires ⬝ frame = Γ.res →
    Expr.WellTyped
      Γ (.tail { callee := .fn (Γ.self.name), args := args })
      (Γ.updateRes (Γ.self.ensures ⬝ frame)) Γ.self.outTys
  /-- Well-typed branching -/
  | wt_branch :
    -- Condition is well-typed
    Γ.vars.get x = some t →
    os.isBoolTy t →
    -- Both branches are well-typed.
    Expr.WellTyped Γ left Γ₁ tys →
    Expr.WellTyped Γ right Γ₂ tys →
    -- The resulting resource should be less than or
    -- equal to the final resources of both branches.
    res' ≤ Γ₁.res →
    res' ≤ Γ₂.res →
    Expr.WellTyped
      Γ (.branch x left right)
      {
        Γ with
        fns := Γ₁.fns.intersect Γ₂.fns,
        res := res'
      } tys
  /-- Well-typed let -/
  | wt_bind :
    Binder.WellTyped Γ binder Γ' →
    Expr.WellTyped Γ' body Γ'' tys →
    Expr.WellTyped Γ (.bind binder body) Γ'' tys

def FnDef.WellTyped {os : OpSet} [PCM os.R] (fns : FnCtx os) (fn : FnDef os) : Prop :=
  ∃ vars' res',
    Expr.WellTyped
      { self := fn, fns, vars := VarCtx.fromTypedVars fn.ins, res := fn.requires }
      fn.body
      { self := fn, fns, vars := vars', res := res' }
      fn.outTys ∧
    res' ≤ fn.ensures

inductive FnCtx.WellTyped {os : OpSet} [PCM os.R] : FnCtx os → Prop where
  | wt_nil : FnCtx.WellTyped []
  | wt_cons :
    FnCtx.WellTyped fns →
    FnDef.WellTyped fns fn →
    FnCtx.WellTyped (fn :: fns)

end Wavelet.L0

-- /-! L1 is similar to L0, except that resources
-- are not kept in a single context, but rather
-- stored and distributed as affine variables. -/
-- namespace Wavelet.L1

-- open Wavelet.Op Wavelet.PCM
-- open Wavelet.L0 (Var Vars FnName TypedVar TypedVars VarCtx)

-- /-
-- ███████╗██╗   ██╗███╗   ██╗████████╗ █████╗ ██╗  ██╗
-- ██╔════╝╚██╗ ██╔╝████╗  ██║╚══██╔══╝██╔══██╗╚██╗██╔╝
-- ███████╗ ╚████╔╝ ██╔██╗ ██║   ██║   ███████║ ╚███╔╝
-- ╚════██║  ╚██╔╝  ██║╚██╗██║   ██║   ██╔══██║ ██╔██╗
-- ███████║   ██║   ██║ ╚████║   ██║   ██║  ██║██╔╝ ██╗
-- ╚══════╝   ╚═╝   ╚═╝  ╚═══╝   ╚═╝   ╚═╝  ╚═╝╚═╝  ╚═╝
-- -/

-- inductive Callee (os : OpSet) where
--   | op : os.Op → Callee os
--   | fn : FnName → Callee os

-- structure Call (os : OpSet) where
--   callee : Callee os
--   args : Vars
--   resource : Var

-- inductive Binder (os : OpSet) where
--   | call : Vars → (resource : Var) → Call os → Binder os
--   | const : Var → os.V → Binder os
--   | join : Var × Var → Var → Binder os
--   | split : Var → Var × Var → Binder os

-- inductive Expr (os : OpSet) where
--   | vars : Vars → Expr os
--   | tail : Call os → Expr os
--   | bind : Binder os → Expr os → Expr os
--   | branch : Var → Expr os → Expr os → Expr os

-- structure FnDef (os : OpSet) where
--   name : FnName
--   ins : TypedVars os.T
--   outTys : List os.T
--   requires : TypedVar os.R
--   ensures : os.R
--   body : Expr os

-- /-
-- ████████╗██╗   ██╗██████╗ ██╗███╗   ██╗ ██████╗      ██████╗ ██████╗ ███╗   ██╗████████╗███████╗██╗  ██╗████████╗
-- ╚══██╔══╝╚██╗ ██╔╝██╔══██╗██║████╗  ██║██╔════╝     ██╔════╝██╔═══██╗████╗  ██║╚══██╔══╝██╔════╝╚██╗██╔╝╚══██╔══╝
--    ██║    ╚████╔╝ ██████╔╝██║██╔██╗ ██║██║  ███╗    ██║     ██║   ██║██╔██╗ ██║   ██║   █████╗   ╚███╔╝    ██║
--    ██║     ╚██╔╝  ██╔═══╝ ██║██║╚██╗██║██║   ██║    ██║     ██║   ██║██║╚██╗██║   ██║   ██╔══╝   ██╔██╗    ██║
--    ██║      ██║   ██║     ██║██║ ╚████║╚██████╔╝    ╚██████╗╚██████╔╝██║ ╚████║   ██║   ███████╗██╔╝ ██╗   ██║
--    ╚═╝      ╚═╝   ╚═╝     ╚═╝╚═╝  ╚═══╝ ╚═════╝      ╚═════╝ ╚═════╝ ╚═╝  ╚═══╝   ╚═╝   ╚══════╝╚═╝  ╚═╝   ╚═╝
-- -/

-- /--
-- For convenience, new `FnDef`s are inserted at the front,
-- i.e., `FnDef`s at the front can only call those at the back.
-- -/
-- abbrev FnCtx os := List (FnDef os)

-- structure Ctx (os : OpSet) where
--   self : FnDef os
--   fns : FnCtx os
--   vars : VarCtx os.T
--   res : VarCtx os.R

-- def Ctx.getFn {os : OpSet} (Γ : Ctx os) (f : FnName) : Option (FnDef os) :=
--   Γ.fns.find? (λ fn => fn.name = f)

-- def Ctx.WellTypedVars {os : OpSet} (Γ : Ctx os) (vs : Vars) (tys : List os.T) : Prop :=
--   List.Forall₂ (λ v t => Γ.vars.get v = some t) vs tys

-- /-
-- ████████╗██╗   ██╗██████╗ ██╗███╗   ██╗ ██████╗     ██████╗ ██╗   ██╗██╗     ███████╗███████╗
-- ╚══██╔══╝╚██╗ ██╔╝██╔══██╗██║████╗  ██║██╔════╝     ██╔══██╗██║   ██║██║     ██╔════╝██╔════╝
--    ██║    ╚████╔╝ ██████╔╝██║██╔██╗ ██║██║  ███╗    ██████╔╝██║   ██║██║     █████╗  ███████╗
--    ██║     ╚██╔╝  ██╔═══╝ ██║██║╚██╗██║██║   ██║    ██╔══██╗██║   ██║██║     ██╔══╝  ╚════██║
--    ██║      ██║   ██║     ██║██║ ╚████║╚██████╔╝    ██║  ██║╚██████╔╝███████╗███████╗███████║
--    ╚═╝      ╚═╝   ╚═╝     ╚═╝╚═╝  ╚═══╝ ╚═════╝     ╚═╝  ╚═╝ ╚═════╝ ╚══════╝╚══════╝╚══════╝
-- -/

-- inductive Call.WellTyped {os : OpSet} [PCM os.R] : Ctx os → Call os → Ctx os → List os.T → os.R → Prop where
--   /-- Well-typed operator call -/
--   | wt_call_op {args} :
--     Γ.WellTypedVars args (os.specOf op).inTys →
--     Γ.res.get resVar = .some (os.specOf op).requires →
--     Call.WellTyped
--       Γ { callee := .op op, args := args, resource := resVar }
--       { Γ with res := Γ.res.remove resVar }
--       (os.specOf op).outTys
--       (os.specOf op).ensures
--   /-- Well-typed function call -/
--   | wt_call_fn {args} :
--     Γ.getFn f = some fn →
--     Γ.WellTypedVars args (TypedVar.ty <$> fn.ins) →
--     Γ.res.get resVar = .some fn.requires.ty →
--     Call.WellTyped
--       Γ { callee := .fn f, args := args, resource := resVar }
--       { Γ with res := Γ.res.remove resVar }
--       fn.outTys
--       fn.ensures

-- inductive Binder.WellTyped {os : OpSet} [PCM os.R] : Ctx os → Binder os → Ctx os → Prop where
--   /-- Well-typed call -/
--   | wt_bind_call {call} :
--     Call.WellTyped Γ call Γ' tys outRes →
--     TypedVars.fromLists vars tys = some typedVars →
--     Binder.WellTyped Γ (.call vars resVar call)
--       { Γ with
--         vars := Γ.vars.insertTypedVars typedVars,
--         res := Γ.res.insert resVar outRes }
--   /-- Well-typed constant binder -/
--   | wt_bind_const :
--     Binder.WellTyped Γ (.const var val)
--       { Γ with vars := Γ.vars.insert var (os.typeOf val) }

-- -- inductive Expr.WellTyped {os : OpSet} [PCM os.R] : Ctx os → Expr os → Ctx os → List os.T → Prop where
-- --   /-- Well-typed variables -/
-- --   | wt_vars :
-- --     Γ.WellTypedVars vs tys →
-- --     Expr.WellTyped Γ (.vars vs) Γ tys
-- --   /-- Well-typed tail call -/
-- --   | wt_tail {Γ' tys} :
-- --     Call.WellTyped Γ c Γ' tys →
-- --     Expr.WellTyped Γ (.tail c) Γ' tys
-- --   /-- Well-typed recursive tail call -/
-- --   | wt_tail_rec :
-- --     Γ.WellTypedVars args (TypedVar.ty <$> Γ.self.ins) →
-- --     Γ.self.requires ⬝ frame = Γ.res →
-- --     Expr.WellTyped
-- --       Γ (.tail { callee := .fn (Γ.self.name), args := args })
-- --       (Γ.updateRes (Γ.self.ensures ⬝ frame)) Γ.self.outTys
-- --   /-- Well-typed branching -/
-- --   | wt_branch :
-- --     -- Condition is well-typed
-- --     Γ.vars.get x = some t →
-- --     os.isBoolTy t →
-- --     -- Both branches are well-typed.
-- --     Expr.WellTyped Γ left Γ₁ tys →
-- --     Expr.WellTyped Γ right Γ₂ tys →
-- --     -- The resulting resource should be less than or
-- --     -- equal to the final resources of both branches.
-- --     res' ≤ Γ₁.res →
-- --     res' ≤ Γ₂.res →
-- --     Expr.WellTyped
-- --       Γ (.branch x left right)
-- --       {
-- --         Γ with
-- --         fns := Γ₁.fns.intersect Γ₂.fns,
-- --         res := res'
-- --       } tys
-- --   /-- Well-typed let -/
-- --   | wt_bind :
-- --     Binder.WellTyped Γ binder Γ' →
-- --     Expr.WellTyped Γ' body Γ'' tys →
-- --     Expr.WellTyped Γ (.bind binder body) Γ'' tys

-- end Wavelet.L1

/-! L1 is a language where the body of each function consists purely of dataflow. -/
namespace Wavelet.L1

open Wavelet.Op Wavelet.PCM

abbrev ProcName := String
abbrev Chan := String

inductive ChanType (os : OpSet) where
  | prim : os.T → ChanType os
  | ghost : os.R → ChanType os

structure TypedChan (T : Type u) where
  name : Chan
  ty : T

abbrev TypedChans (T : Type u) := List (TypedChan T)

inductive Proc (os : OpSet) where
  | Inact : Proc os
  | Par (p₁ : Proc os) (p₂ : Proc os) : Proc os
  | New (c : Chan) (ty : ChanType os) (p : Proc os) : Proc os
  | Operator (op : os.Op) (ins : List Chan) (outs : List Chan) (resIn : Chan) (resOut : Chan) : Proc os
  | Steer (expected : Bool) (decider : Chan) (input : Chan) (output : Chan) : Proc os
  | Merge (decider : Chan) (input₁ : Chan) (input₂ : Chan) (output : Chan) : Proc os
  | Fork (input : Chan) (output₁ : Chan) (output₂ : Chan) : Proc os
  | Const (val : os.V) (act : Chan) (output : Chan) : Proc os
  | Sink (input : Chan) : Proc os
  | Forward (input : Chan) (output : Chan) : Proc os

structure ProcDef (os : OpSet) where
  name : ProcName
  ins : TypedChans (ChanType os)
  outs : List os.T
  body : Proc os

end Wavelet.L1
