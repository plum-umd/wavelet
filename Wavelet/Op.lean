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
  | Ret : R → ITree E R
  | Fix {A B : Type w} : (A → ITree E (A ⊕ B)) → A → (B → ITree E R) → ITree E R
  | Vis : E A → (A → ITree E R) → ITree E R

def ITree.bind {A B : Type u} (t : ITree E A) (f : A → ITree E B) : ITree E B :=
  match t with
  | ITree.Ret r => f r
  | ITree.Fix m i k => ITree.Fix m i (λ x => (k x).bind f)
  | ITree.Vis e k => ITree.Vis e (λ x => (k x).bind f)

instance : Monad (ITree E) where
  pure := ITree.Ret
  bind := ITree.bind

/-- Constructs an itree that represents the semantics of iterating `body` until it returns `inr`. -/
def ITree.iter (body : A → ITree E (A ⊕ B)) : A → ITree E B :=
  λ init => ITree.Fix body init ITree.Ret

-- inductive ITree (E : Type u → Type v) (R : Type w) where
--   | Ret : R → ITree E R
--   | Tau : ITree E R → ITree E R
--   | Vis {X : Type u} : E X → (X → ITree E R) → ITree E R

-- def ITree.bind (t : ITree E A) (f : A → ITree E B) : ITree E B :=
--   match t with
--   | ITree.Ret r => f r
--   | ITree.Tau t' => ITree.Tau (t'.bind f)
--   | ITree.Vis e k => ITree.Vis e (λ x => (k x).bind f)

-- instance : Monad (ITree E) where
--   pure := ITree.Ret
--   bind := ITree.bind

-- instance [Inhabited R] : Inhabited (ITree E R) where
--   default := ITree.Ret default

-- -- instance[Bind E] [∀ α, Lean.Order.PartialOrder (ITree E α)] : Lean.Order.MonoBind (ITree E) where
-- --   bind_mono_left := sorry
-- --   bind_mono_right := sorry

-- open Lean.Order

-- def ITree.iter [Inhabited A] [Inhabited B] (body : A → ITree E (A ⊕ B)) : A → ITree E B :=
--   λ init => do
--     let r ← body init
--     match r with
--     | .inl a => ITree.iter body a
--     | .inr b => ITree.Ret b
--   partial_fixpoint monotonicity by
--     monotonicity
--     intros x y hxy
--     simp only
--     sorry

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
  | tail : Vars → Expr os
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
abbrev VarMap (T : Type u) := Var → Option T

def VarMap.get (x : Var) (vars : VarMap T) : Option T := vars x

def VarMap.insert (x : Var) (t : T) (vars : VarMap T) : VarMap T :=
  λ y => if y = x then some t else vars y

def VarMap.remove (x : Var) (vars : VarMap T): VarMap T :=
  λ y => if y = x then none else vars y

def VarMap.insertTypedVars (vs : TypedVars T) (vars : VarMap T) : VarMap T :=
  vs.foldl (λ ctx v => ctx.insert v.name v.ty) vars

def VarMap.fromTypedVars (vs : TypedVars T) : VarMap T :=
  λ x => TypedVar.ty <$> vs.find? (λ v => v.name = x)

def VarMap.fromKVs (kvs : List (Var × T)) : VarMap T :=
  λ x => (kvs.find? (λ (k, _) => k = x)).map Prod.snd

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
  /-- Well-typed recursive tail call -/
  | wt_tail :
    Γ.WellTypedVars args (TypedVar.ty <$> Γ.self.ins) →
    Γ.self.requires ⬝ frame = Γ.res →
    Expr.WellTyped
      Γ (.tail args)
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
      { self := fn, fns, vars := VarMap.fromTypedVars fn.ins, res := fn.requires }
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

/-- Attaches a local state and makes the operator monad fallible. -/
abbrev InterpM (os : OpSet) (M) [Monad M] := StateT (VarMap os.V) (OptionT M)

/-- TODO: add error types -/
def InterpM.fail {os : OpSet} {M} [instM : Monad M] : InterpM os M α :=
  StateT.lift (instM.pure none)

def InterpM.getVar {os : OpSet} {M} [Monad M] (v : Var) : InterpM os M os.V := do
  let vars ← get
  match vars.get v with
  | some val => return val
  | none => InterpM.fail

def InterpM.setVar {os : OpSet} {M} [Monad M] (v : Var) (val : os.V) : InterpM os M Unit :=
  modify (VarMap.insert v val)

def InterpM.lift {os : OpSet} {M} [Monad M] {α : Type u} : M α → InterpM os M α :=
  StateT.lift ∘ OptionT.lift

/-! TODO: use itrees instead, as we can't prove anything useful about partial functions -/
mutual

def Expr.callFn
  {os : OpSet} {M} [Monad M] [PCM os.R] [OpSemantics os M]
  (fns : FnCtx os)
  (self : FnDef os)
  (callee : FnDef os)
  (args : Vars) : InterpM os M (List os.V) := do
  let vals ← args.mapM InterpM.getVar
  if vals.length ≠ callee.ins.length then
    InterpM.fail
  else
    let init := VarMap.fromKVs (List.zip (TypedVar.name <$> self.ins) vals)
    let (ret, _) ← StateT.lift ((self.body.interpret fns self).run init)
    return ret
partial_fixpoint monotonicity
  sorry

def Call.interpret
  {os : OpSet} {M} [Monad M] [PCM os.R] [OpSemantics os M]
  (fns : FnCtx os)
  (call : Call os) : InterpM os M (List os.V) :=
  match call.callee with
  | .op op => do
    let vals ← call.args.mapM InterpM.getVar
    InterpM.lift (OpSemantics.runOp op vals)
  | .fn fn =>
    match fns.getFn fn with
    | none => InterpM.fail
    | some callee =>
      Expr.callFn fns callee callee call.args
partial_fixpoint monotonicity sorry

def Binder.interpret
  {os : OpSet} {M} [Monad M] [PCM os.R] [OpSemantics os M]
  (fns : FnCtx os) :
  Binder os → InterpM os M Unit
  | .call vars call => do
    let vals ← call.interpret fns
    if vals.length ≠ vars.length then
      InterpM.fail
    else
      -- Bind the return values
      (vars.zip vals).forM (λ (var, val) => InterpM.setVar var val)
  | .const var val =>
    modify (VarMap.insert var val)
partial_fixpoint monotonicity sorry

def Expr.interpret
  {os : OpSet} {M} [Monad M] [PCM os.R] [OpSemantics os M]
  (fns : FnCtx os)
  (self : FnDef os) :
  Expr os → InterpM os M (List os.V)
  | .vars vs => vs.mapM InterpM.getVar
  | .tail args => Expr.callFn fns self self args
  | .bind binder cont => binder.interpret fns *> cont.interpret fns self
  | .branch cond left right => do
    let v ← InterpM.getVar cond
    match os.asBool v with
    | none => InterpM.fail
    | some b => if b then left.interpret fns self else right.interpret fns self
partial_fixpoint monotonicity sorry

end -- mutual

-- theorem test
--   {os : OpSet} {M} [Monad M] [PCM os.R] [OpSemantics os M]
--   (fns : FnCtx os)
--   (self : FnDef os)
--   (e : Expr os) :
--   e.interpret fns self = e.interpret (M := M) fns self := by
--   unfold Expr.interpret
--   sorry

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
