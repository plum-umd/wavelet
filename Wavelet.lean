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

/-! Basic definitions of interaction trees. -/
namespace Wavelet.ITree

/-- An inductive version of interaction trees with an explicit fixpoint constructor. -/
inductive ITree (E : Type u → Type v) : Type w → Type (max (u + 1) v (w + 2)) where
  | ret : R → ITree E R
  | fix {A B : Type w} : (A → ITree E (A ⊕ B)) → A → (B → ITree E R) → ITree E R
  | vis : E A → (A → ITree E R) → ITree E R

def ITree.bind {A B : Type u} (t : ITree E A) (f : A → ITree E B) : ITree E B :=
  match t with
  | .ret r => f r
  | .fix m i k => .fix m i (λ x => (k x).bind f)
  | .vis e k => .vis e (λ x => (k x).bind f)

instance : Monad (ITree E) where
  pure := .ret
  bind := .bind

def ITree.lift (e : E A) : ITree E A := .vis e .ret

/-- Short-hand for iterating the given function until it returns `inr` -/
def ITree.iter {A B : Type u} (f : A → ITree E (A ⊕ B)) (a : A) : ITree E B := .fix f a .ret

instance : LawfulFunctor (ITree E) where
  map_const := rfl
  id_map := by
    intros _ x
    simp only [Functor.map]
    induction x with
    | ret r => rfl
    | fix m i k ih ih2 =>
      simp only [ITree.bind, Function.comp_id, ITree.fix.injEq, heq_eq_eq, true_and]
      funext
      apply ih2
    | vis e k ih =>
      simp only [ITree.bind, Function.comp_id, ITree.vis.injEq, heq_eq_eq, true_and]
      funext
      apply ih
  comp_map := by
    intros _ _ _ g h x
    simp only [Functor.map]
    induction x with
    | ret r => rfl
    | fix m i k ih ih2 =>
      simp only [ITree.bind, ITree.fix.injEq, heq_eq_eq, true_and]
      funext
      apply ih2
    | vis e k ih =>
      simp only [ITree.bind, ITree.vis.injEq, heq_eq_eq, true_and]
      funext
      apply ih

/- TODO: prove LawfulApplicative and LawfulMonad -/

end Wavelet.ITree

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

class OpSemantics (os : OpSet) [PCM os.R] (M : Type u → Type v) [Monad M] where
  /-- Interpret the semantics of operators in a custom monad. -/
  runOp : os.Op → List os.V → M (List os.V)

  /-- The operator's declared resource spec should be frame-preserving.  -/
  op_valid_res_spec (op : os.Op) : (os.specOf op).requires ⟹ (os.specOf op).ensures

  /- If resource inputs to two operators are disjoint, their interpretations commute. -/
  op_disj_commute (op₁ op₂ : os.Op) (ins₁ ins₂ : List os.V)
    (hwt_ins₁ : os.WellTypedValues ins₁ (os.specOf op₁).inTys)
    (hwt_ins₂ : os.WellTypedValues ins₂ (os.specOf op₂).inTys)
    (hdisj : (os.specOf op₁).requires ⊥ (os.specOf op₂).requires) :
    ∀ (s : M T),
      s *> (Prod.mk <$> runOp op₁ ins₁ <*> runOp op₂ ins₂) =
      s *> (Prod.mk <$> runOp op₂ ins₂ <*> runOp op₁ ins₁)
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

inductive Expr (os : OpSet) where
  | vars : Vars → Expr os
  | tail : Vars → Expr os
  | let_fn : (boundVars : Vars) → FnName → (args : Vars) → Expr os → Expr os
  | let_op : (boundVars : Vars) → os.Op → (args : Vars) → Expr os → Expr os
  | let_const : Var → os.V → Expr os → Expr os
  | branch : Var → Expr os → Expr os → Expr os

structure FnDef (os : OpSet) where
  name : FnName
  ins : List (Var × os.T)
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
abbrev VarMap (T : Type u) := Var → Option T

def VarMap.get (x : Var) (vars : VarMap T) : Option T := vars x

def VarMap.insert (x : Var) (t : T) (vars : VarMap T) : VarMap T :=
  λ y => if y = x then some t else vars y

def VarMap.remove (x : Var) (vars : VarMap T): VarMap T :=
  λ y => if y = x then none else vars y

def VarMap.fromList (vs : List (Var × T)) : VarMap T :=
  λ x => (vs.find? (λ (k, _) => k = x)).map Prod.snd

def VarMap.insertVars (vs : List (Var × T)) (vars : VarMap T) : VarMap T :=
  λ x => (VarMap.fromList vs).get x <|> vars x

/--
For convenience, new `FnDef`s are inserted at the front,
i.e., `FnDef`s at the front can only call those at the back.
-/
abbrev FnCtx os := List (FnDef os)

structure Ctx (os : OpSet) where
  self : FnDef os
  fns : FnCtx os
  vars : VarMap os.T
  res : os.R

def FnCtx.intersect {os : OpSet} (fns₁ fns₂ : FnCtx os) : FnCtx os :=
  fns₁.filter (λ fn₁ => fns₂.any (λ fn₂ => fn₁.name = fn₂.name))

def FnCtx.getFn {os : OpSet} (fns : FnCtx os) (f : FnName) : Option (FnDef os) :=
  fns.find? (λ fn => fn.name = f)

def Ctx.WellTypedVars {os : OpSet} (Γ : Ctx os) (vs : Vars) (tys : List os.T) : Prop :=
  List.Forall₂ (λ v t => Γ.vars.get v = some t) vs tys

def Ctx.getFn {os : OpSet} (Γ : Ctx os) (f : FnName) : Option (FnDef os) := Γ.fns.getFn f

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

inductive Expr.WellTyped {os : OpSet} [PCM os.R] : Ctx os → Expr os → Ctx os → List os.T → Prop where
  /-- Well-typed variables -/
  | wt_vars :
    Γ.WellTypedVars vs tys →
    Expr.WellTyped Γ (.vars vs) Γ tys
  /-- Well-typed recursive tail call -/
  | wt_tail :
    Γ.WellTypedVars args (Prod.snd <$> Γ.self.ins) →
    Γ.self.requires ⬝ frame = Γ.res →
    Expr.WellTyped
      Γ (.tail args)
      (Γ.updateRes (Γ.self.ensures ⬝ frame)) Γ.self.outTys
  /-- Well-typed let fn call -/
  | wt_let_fn :
    Γ.getFn fnName = some fn →
    Γ.WellTypedVars args (Prod.snd <$> fn.ins) →
    fn.requires ⬝ frame = Γ.res →
    boundVars.length = fn.outTys.length →
    Expr.WellTyped {
      Γ with
      res := fn.ensures ⬝ frame,
      vars := Γ.vars.insertVars (boundVars.zip fn.outTys)
    } cont Γ' tys →
    Expr.WellTyped Γ (.let_fn boundVars fnName args cont) Γ' tys
  /-- Well-typed let op call -/
  | wt_let_op :
    Γ.WellTypedVars args (os.specOf op).inTys →
    (os.specOf op).requires ⬝ frame = Γ.res →
    boundVars.length = (os.specOf op).outTys.length →
    Expr.WellTyped {
      Γ with
      res := (os.specOf op).ensures ⬝ frame,
      vars := Γ.vars.insertVars (boundVars.zip (os.specOf op).outTys)
    } cont Γ' tys →
    Expr.WellTyped Γ (.let_op boundVars op args cont) Γ' tys
  /-- Well-typed let constant -/
  | wt_let_const :
    Expr.WellTyped {
      Γ with
      vars := Γ.vars.insert var (os.typeOf val)
    } cont Γ' tys →
    Expr.WellTyped Γ (.let_const var val cont) Γ' tys
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

def FnDef.WellTyped {os : OpSet} [PCM os.R] (fns : FnCtx os) (fn : FnDef os) : Prop :=
  ∃ vars' res',
    Expr.WellTyped
      { self := fn, fns, vars := VarMap.fromList fn.ins, res := fn.requires }
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

/-
███████╗███████╗███╗   ███╗ █████╗ ███╗   ██╗████████╗██╗ ██████╗███████╗
██╔════╝██╔════╝████╗ ████║██╔══██╗████╗  ██║╚══██╔══╝██║██╔════╝██╔════╝
███████╗█████╗  ██╔████╔██║███████║██╔██╗ ██║   ██║   ██║██║     ███████╗
╚════██║██╔══╝  ██║╚██╔╝██║██╔══██║██║╚██╗██║   ██║   ██║██║     ╚════██║
███████║███████╗██║ ╚═╝ ██║██║  ██║██║ ╚████║   ██║   ██║╚██████╗███████║
╚══════╝╚══════╝╚═╝     ╚═╝╚═╝  ╚═╝╚═╝  ╚═══╝   ╚═╝   ╚═╝ ╚═════╝╚══════╝
-/

open Wavelet.ITree

/-- Evaluation result of an expression -/
inductive Expr.EvalResult (os : OpSet) where
  | ret : List os.V → EvalResult os
  | tail : List os.V → EvalResult os
  | err : EvalResult os

mutual

variable {os : OpSet} [PCM os.R]
variable {M} [Monad M]
variable [OpSemantics os M]

def Expr.interpretFn
  (fns : FnCtx os)
  (fnName : FnName)
  (args : List os.V) : ITree M (Option (List os.V)) :=
  match fns with
  | [] => return none
  | fn :: fns' =>
    if fn.name = fnName then
      fn.interpret fns' args
    else
      Expr.interpretFn fns' fnName args

/-- Interprets an expression as an `ITree` in the given `OpSemantics`. -/
def Expr.interpret
  (fns : FnCtx os)
  (self : FnDef os)
  (locals : VarMap os.V) :
  Expr os → ITree M (Expr.EvalResult os)
  | .vars vs =>
    return match vs.mapM locals.get with
      | some vals => .ret vals
      | none => .err
  | .tail args =>
    return match args.mapM locals.get with
      | some vals => .tail vals
      | none => .err
  | .let_fn boundVars fnName args cont =>
    match args.mapM locals.get with
    | some args => do
      let retVals ← Expr.interpretFn fns fnName args
      match retVals with
      | some retVals =>
        if boundVars.length = retVals.length then
          cont.interpret fns self (locals.insertVars (boundVars.zip retVals))
        else
          return .err
      | none => return .err
    | none => return .err
  | .let_op boundVars op args cont =>
    match args.mapM locals.get with
    | some args => do
      let retVals ← ITree.lift (OpSemantics.runOp op args)
      if boundVars.length = retVals.length then
        cont.interpret fns self (locals.insertVars (boundVars.zip retVals))
      else
        return .err
    | none => return .err
  | .let_const var val cont =>
    cont.interpret fns self (locals.insert var val)
  | .branch cond left right =>
    if let some v := locals.get cond then
      if let some b := os.asBool v then
        if b then
          left.interpret fns self locals
        else
          right.interpret fns self locals
      else return .err
    else
      return .err

def FnDef.interpret
  (fns : FnCtx os)
  (self : FnDef os)
  (args : List os.V) : ITree M (Option (List os.V)) :=
  -- Interpreted as the fixpoint of repeatedly applying tail calls until return
  ITree.iter (λ args =>
    if args.length = self.ins.length then do
      let locals := VarMap.fromList (List.zip (self.ins.map Prod.fst) args)
      match ← self.body.interpret fns self locals with
      | .ret vals => return .inr (some vals)
      | .tail vals => return .inl vals
      | .err => return .inr none
    else
      return .inr none)
    args

end -- mutual

end Wavelet.L0

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
