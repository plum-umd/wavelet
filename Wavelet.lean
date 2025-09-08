import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

set_option linter.dupNamespace false

/-! A formulation of partial commutative monoids. -/
namespace Wavelet.PCM

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
  /-- Convert a value to bool -/
  asBool : V → Option Bool
  /-- `asBool` behaves correctly -/
  asBool_correct : ∀ v, isBoolTy (typeOf v) ↔ (asBool v).isSome

def OpSet.WellTypedValues (os : OpSet) (ins : List os.V) (inTys : List os.T) : Prop :=
  List.Forall₂ (λ v t => os.typeOf v = t) ins inTys

abbrev OpM S R := StateT S Option R

class OpSemantics (os : OpSet) [PCM os.R] where
  S : Type w

  /-- TODO: generalize to custom monads? -/
  runOp : os.Op → List os.V → OpM S (List os.V)

  /-- The operator's declared resource spec should be frame-preserving.  -/
  op_valid_res_spec (op : os.Op) : (os.specOf op).requires ⟹ (os.specOf op).ensures

  /- If resource inputs to two operators are disjoint, their interpretations commute. -/
  op_disj_commute (op₁ op₂ : os.Op) (ins₁ ins₂ : List os.V)
    (hwt_ins₁ : os.WellTypedValues ins₁ (os.specOf op₁).inTys)
    (hwt_ins₂ : os.WellTypedValues ins₂ (os.specOf op₂).inTys)
    (hdisj : (os.specOf op₁).requires ⊥ (os.specOf op₂).requires) :
    ∀ (s : OpM S R),
      s *> (Prod.mk <$> runOp op₁ ins₁ <*> runOp op₂ ins₂) =
      s *> (Prod.mk <$> runOp op₂ ins₂ <*> runOp op₁ ins₁)

end Wavelet.Op

/-! Syntax and typing rules of L0, a first-order sequential language with affine resources. -/
namespace Wavelet.L0

open Wavelet.Op Wavelet.PCM

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

/-- Typing rules -/
inductive Expr.WellTyped {os : OpSet} [PCM os.R] : Ctx os → Expr os → Ctx os → List os.T → Prop where
  /-- Well-typed variables -/
  | wt_vars :
    Γ.WellTypedVars vs tys →
    Expr.WellTyped Γ (.vars vs) Γ tys
  /-- Well-typed recursive tail call -/
  | wt_tail :
    Γ.WellTypedVars args (Prod.snd <$> Γ.self.ins) →
    Γ.self.requires ⬝ frame ≡ Γ.res →
    Expr.WellTyped
      Γ (.tail args)
      (Γ.updateRes (Γ.self.ensures ⬝ frame)) Γ.self.outTys
  /-- Well-typed let fn call -/
  | wt_let_fn :
    Γ.getFn fnName = some fn →
    Γ.WellTypedVars args (Prod.snd <$> fn.ins) →
    fn.requires ⬝ frame ≡ Γ.res →
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
    (os.specOf op).requires ⬝ frame ≡ Γ.res →
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

end Wavelet.L0

/-! Small-step operational semantics of L0. -/
namespace Wavelet.L0

open PCM Op L0

variable (os : OpSet) [PCM os.R]
variable [sem : OpSemantics os]

inductive Label where
  | op : os.Op → List os.V → Label
  | tau : Label

/-- A saved stack frame. -/
structure Frame where
  locals : VarMap os.V
  expr : Expr os
  fn : FnDef os
  contVars : Vars

structure Stack where
  frames : List (Frame os)
  locals : VarMap os.V
  fn : FnDef os

inductive Config where
  | ret : FnCtx os → sem.S → Stack os → List os.V → Config
  | expr : FnCtx os → sem.S → Stack os → Expr os → Config

inductive Step : Config os → Label os → Config os → Prop where
  | step_vars :
    (vars.mapM stack.locals.get = some vals) →
    Step
      (Config.expr fns state stack (.vars vars))
      .tau
      (Config.ret fns state stack vals)
  | step_ret :
    stack.frames = frame :: restFrames →
    frame.contVars.length = vals.length →
    -- Restore the previous frame
    Step
      (Config.ret fns state stack vals)
      .tau
      (Config.expr fns state { stack with
        frames := restFrames,
        locals := frame.locals.insertVars (frame.contVars.zip vals)
        fn := frame.fn
      } frame.expr)
  | step_tail :
    args.length = stack.fn.ins.length →
    (args.mapM stack.locals.get = some vals) →
    Step
      (Config.expr fns state stack (.tail args))
      .tau
      (Config.expr fns state { stack with
        locals := VarMap.fromList ((stack.fn.ins.map Prod.fst).zip vals),
      } stack.fn.body)
  | step_let_fn :
    fns.getFn fnName = some fn →
    args.length = fn.ins.length →
    (args.mapM stack.locals.get = some vals) →
    Step
      (Config.expr fns state stack (.let_fn boundVars fnName args cont))
      .tau
      -- Save current frame and continue with the new function
      (Config.expr fns state { stack with
        frames := {
          contVars := boundVars,
          expr := cont,
          fn := stack.fn,
          locals := stack.locals
        } :: stack.frames,
        locals := VarMap.fromList ((fn.ins.map Prod.fst).zip vals),
      } stack.fn.body)
  | step_let_op :
    args.length = (os.specOf op).inTys.length →
    (args.mapM stack.locals.get = some vals) →
    (sem.runOp op vals).run state = some (outVals, newState) →
    outVals.length = boundVars.length →
    Step
      (Config.expr fns state stack (.let_op boundVars op args cont))
      (Label.op op vals)
      (Config.expr fns newState { stack with
        locals := stack.locals.insertVars (boundVars.zip outVals)
      } cont)
  | step_let_const :
    Step
      (Config.expr fns state stack (.let_const var val cont))
      .tau
      (Config.expr fns state { stack with
        locals := stack.locals.insert var val
      } cont)
  | step_branch :
    stack.locals.get condVar = some condVal →
    os.asBool condVal = some condBool →
    Step
      (Config.expr fns state stack (.branch condVar left right))
      .tau
      (Config.expr fns state stack (if condBool then left else right))

inductive StepStar : Config os → List (Label os) → Config os → Prop where
  | refl : StepStar c [] c
  | step :
    Step os c₁ l c₂ →
    StepStar c₂ l' c₃ →
    StepStar c₁ (l :: l') c₃

/-- Final configuration -/
inductive Final : Config os → sem.S → List os.V → Prop where
  | final :
    stack.frames = [] →
    Final (Config.ret _ state stack vals) state vals

end Wavelet.L0

/-! Syntax and operational semantics of L1. -/
namespace Wavelet.L1

open PCM Op

variable (os : OpSet)

abbrev ProcName := String
abbrev Chan := L0.Var

inductive ChanType (os : OpSet) where
  | prim : os.T → ChanType os
  | ghost : os.R → ChanType os

structure TypedChan (T : Type u) where
  name : Chan
  ty : T

inductive AtomicProc where
  | op (op : os.Op) (ins : List Chan) (outs : List Chan) (resIn : Chan) (resOut : Chan) : AtomicProc
  | steer (expected : Bool) (decider : Chan) (input : Chan) (output : Chan) : AtomicProc
  | carry (decider : Chan) (input₁ : Chan) (input₂ : Chan) (output : Chan) : AtomicProc
  | merge (decider : Chan) (input₁ : Chan) (input₂ : Chan) (output : Chan) : AtomicProc
  | fork (input : Chan) (output₁ : Chan) (output₂ : Chan) : AtomicProc
  | const (val : os.V) (act : Chan) (output : Chan) : AtomicProc
  | sink (input : Chan) : AtomicProc
  | forward (input : Chan) (output : Chan) : AtomicProc

abbrev Proc := Finset (AtomicProc os)

inductive Token where
  | val : os.V → Token
  | res : os.R → Token

abbrev ChanMap := L0.VarMap
abbrev ChanState (os : OpSet) := ChanMap (List (Token os))

variable [PCM os.R] [sem : OpSemantics os]

inductive Label where
  | op : os.Op → List os.V → Label
  | tau : Label

structure Config where
  proc : Proc os
  chans : ChanState os
  state : sem.S

def ChanState.pop (c : Chan) : StateT (ChanState os) Option (Token os) := do
  let chans ← get
  match chans.get c with
  | some (v :: vs) => do
    set (chans.insert c vs)
    return v
  | _ => StateT.lift none

def ChanState.popValue (c : Chan) : StateT (ChanState os) Option os.V := do
  let tok ← ChanState.pop os c
  match tok with
  | .val v => return v
  | .res _ => StateT.lift none

def ChanState.popRes (c : Chan) : StateT (ChanState os) Option os.R := do
  let tok ← ChanState.pop os c
  match tok with
  | .res r => return r
  | .val _ => StateT.lift none

def ChanState.push (c : Chan) (v : Token os) : StateT (ChanState os) Option Unit := do
  let chans ← get
  match chans.get c with
  | some vs => set (chans.insert c (vs ++ [v]))
  | none => set (chans.insert c [v])

inductive Step : Config os → Label os → Config os → Prop where
  | step_op :
    (.op op ins outs resIn resOut) ∈ c.proc →
    -- Read input values
    (ins.mapM (λ inChan => ChanState.popValue os inChan)).run c.chans = some (inVals, newChans) →
    -- Read input resource
    (ChanState.popRes os resIn).run newChans = some (inRes, newChans') →
    -- Run the operator
    (sem.runOp op inVals).run c.state = some (outVals, newState) →
    -- Write output values
    outVals.length = outs.length →
    ((outs.zip outVals).mapM (λ (outChan, outVal) =>
      ChanState.push os outChan (.val outVal))).run newChans' = some (_, newChans'') →
    -- Write output resource
    (ChanState.push os resOut (.res (os.specOf op).ensures)).run newChans'' = some (_, finalChans) →
    Step c .tau { c with
      chans := finalChans,
      state := newState
    }
  /- TODO: more rules -/

end Wavelet.L1
