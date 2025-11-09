import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.UnionInter

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
  T : Type
  /-- Base values -/
  V : Type
  /-- Ghost resource types -/
  R : Type
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
  S : Type

  /-- TODO: generalize to custom monads? -/
  interpOp : os.Op → List os.V → OpM S (List os.V)

  /-- The operator's declared resource spec should be frame-preserving.  -/
  op_valid_res_spec (op : os.Op) : (os.specOf op).requires ⟹ (os.specOf op).ensures

  /- If resource inputs to two operators are disjoint, their interpretations commute. -/
  op_disj_commute (op₁ op₂ : os.Op) (ins₁ ins₂ : List os.V)
    (hwt_ins₁ : os.WellTypedValues ins₁ (os.specOf op₁).inTys)
    (hwt_ins₂ : os.WellTypedValues ins₂ (os.specOf op₂).inTys)
    (hdisj : (os.specOf op₁).requires ⊥ (os.specOf op₂).requires) :
    ∀ (s : OpM S R),
      s *> (Prod.mk <$> interpOp op₁ ins₁ <*> interpOp op₂ ins₂) =
      s *> (Prod.mk <$> interpOp op₂ ins₂ <*> interpOp op₁ ins₁)

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

def VarMap.insertOption (x : Var) (t : Option T) (vars : VarMap T) : VarMap T :=
  λ y => if y = x then t else vars y

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
    (sem.interpOp op vals).run state = some (outVals, newState) →
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

/-! A monadic semantics of L0. -/
namespace Wavelet.L0

open PCM Op L0

/-- An inductive version of interaction trees with an explicit fixpoint constructor. -/
inductive FixTree (E : Type u → Type v) : Type w → Type (max (u + 1) v (w + 2)) where
  | ret : R → FixTree E R
  | vis : E A → (A → FixTree E R) → FixTree E R
  | fix {A B : Type w} : (A → FixTree E (A ⊕ B)) → A → (B → FixTree E R) → FixTree E R

/-- Types of next actions allowed in any `FixTree`. -/
inductive FixTreeShape (E : Type u → Type v) : Type w → Type (max (u + 1) v (w + 2)) where
  | ret : R → FixTreeShape E R
  | tau : FixTree E R → FixTreeShape E R
  | vis : E A → (A → FixTree E R) → FixTreeShape E R

def FixTree.bind {A B : Type u} (t : FixTree E A) (f : A → FixTree E B) : FixTree E B :=
  match t with
  | .ret r => f r
  | .vis e k => .vis e (λ x => (k x).bind f)
  | .fix m i k => .fix m i (λ x => (k x).bind f)

instance : Monad (FixTree E) where
  pure := .ret
  bind := .bind

/-- Destructs/unfolds a `FixTree` to get `FixTreeShape`. -/
def FixTree.destruct (t : FixTree E R) : FixTreeShape E R :=
  match t with
  | .ret r => .ret r
  | .vis e k => .vis e k
  | .fix m i k =>
    -- Try to get the next action of the inner iteration.
    match FixTree.destruct (m i) with
    -- Inner iteration decides to continute the loop without any action.
    | .ret (.inl a) => .tau (FixTree.fix m a k)
    -- Inner iteration terminates without action.
    | .ret (.inr b) => FixTree.destruct (k b)
    -- Inner iteration emits a silent action
    | .tau t => .tau do
      match ← t with
      | .inl a => FixTree.fix m a k
      | .inr b => k b
    -- Inner iteration emits a visible action
    | .vis e m' => .vis e (λ x => do
      match ← m' x with
      | .inl a => FixTree.fix m a k
      | .inr b => k b)

def FixTree.trigger (e : E A) : FixTree E A := .vis e .ret

/-- Short-hand for iterating the given function until it returns `inr` -/
def FixTree.iter {A B : Type u} (f : A → FixTree E (A ⊕ B)) (a : A) : FixTree E B := .fix f a .ret

/-- Final evaluation result of an expression. -/
inductive Expr.EvalResult (os : OpSet) where
  | ret : List os.V → EvalResult os
  | tail : List os.V → EvalResult os

/-- Evaluation event. -/
inductive Expr.EvalE (os : OpSet) : Type → Type where
  | op : os.Op → List os.V → EvalE os (List os.V)

/-- Evaluation monad for expressions. -/
abbrev Expr.EvalM os := StateT (VarMap os.V) (OptionT (FixTree (Expr.EvalE os)))

def Expr.EvalM.err {os : OpSet} : EvalM os R := StateT.lift OptionT.fail

def Expr.EvalM.getLocal {os : OpSet} (x : Var) : EvalM os (os.V) := do
  let locals ← get
  match locals.get x with
  | some v => return v
  | none => .err

def Expr.EvalM.setLocal {os : OpSet} (x : Var) (v : os.V) : EvalM os Unit := do
  let locals ← get
  set (locals.insert x v)

/-- Evaluation monad for function definitions. -/
abbrev FnDef.EvalM os := OptionT (FixTree (Expr.EvalE os))

mutual

variable {os : OpSet}

def Expr.interpretFn
  (fns : FnCtx os)
  (fnName : FnName)
  (args : List os.V) : Expr.EvalM os (List os.V) :=
  match fns with
  | [] => .err
  | fn :: fns' =>
    if fn.name = fnName then
      .lift (fn.interpret fns' args)
    else
      Expr.interpretFn fns' fnName args

/--
Interprets an expression as an `ITree` in the given `OpSemantics`.
Local variable reads/writes are interpreted directly through a "state monad"
on `VarMap os.V` without `ITree` events.
-/
def Expr.interpret
  (fns : FnCtx os)
  (self : FnDef os) :
  Expr os → Expr.EvalM os (Expr.EvalResult os)
  | .vars vs => .ret <$> vs.mapM .getLocal
  | .tail args => .tail <$> args.mapM .getLocal
  | .let_fn boundVars fnName args cont => do
    let argVals ← args.mapM .getLocal
    let retVals ← Expr.interpretFn fns fnName argVals
    if boundVars.length = retVals.length then
      (boundVars.zip retVals).forM (λ (v, val) => .setLocal v val)
      cont.interpret fns self
    else
      .err
  | .let_op boundVars op args cont => do
    let argVals ← args.mapM .getLocal
    let retVals ← .lift (.lift (.trigger (.op op argVals)))
    if boundVars.length = retVals.length then
      (boundVars.zip retVals).forM (λ (v, val) => .setLocal v val)
      cont.interpret fns self
    else
      .err
  | .let_const var val cont => do
    .setLocal var val
    cont.interpret fns self
  | .branch cond left right => do
    let condVal ← .getLocal cond
    if let some b := os.asBool condVal then
      if b then
        left.interpret fns self
      else
        right.interpret fns self
    else
      .err

def FnDef.interpret
  (fns : FnCtx os)
  (self : FnDef os)
  (args : List os.V) : FnDef.EvalM os (List os.V) :=
  -- Interpreted as the fixpoint of repeatedly applying tail calls until return
  FixTree.iter (λ args =>
    if args.length = self.ins.length then do
      let locals := VarMap.fromList (List.zip (self.ins.map Prod.fst) args)
      let evalRes ← self.body.interpret fns self locals
      match evalRes with
      | some (.ret vals, _) => return .inr (some vals)
      | some (.tail vals, _) => return .inl vals
      | none => return .inr none
    else
      return .inr none)
    args

end -- mutual

end Wavelet.L0

/-! Syntax and operational semantics of L1. -/
namespace Wavelet.L1

open PCM Op

variable (os : OpSet)
variable [DecidableEq os.Op] [DecidableEq os.V]

abbrev ProcName := String
abbrev Chan := L0.Var

inductive ChanType (os : OpSet) where
  | prim : os.T → ChanType os
  | ghost : os.R → ChanType os

structure TypedChan (T : Type u) where
  name : Chan
  ty : T

inductive AtomicProc [DecidableEq os.Op] [DecidableEq os.V] where
  | op (op : os.Op) (ins : List Chan) (outs : List Chan) (resIn : Chan) (resOut : Chan) : AtomicProc
  | steer (expected : Bool) (decider : Chan) (input : Chan) (output : Chan) : AtomicProc
  | carry (decider : Chan) (input₁ : Chan) (input₂ : Chan) (output : Chan) : AtomicProc
  | merge (decider : Chan) (input₁ : Chan) (input₂ : Chan) (output : Chan) : AtomicProc
  | fork (input : Chan) (output₁ : Chan) (output₂ : Chan) : AtomicProc
  | const (val : os.V) (act : Chan) (output : Chan) : AtomicProc
  | sink (input : Chan) : AtomicProc
  | forward (input : Chan) (output : Chan) : AtomicProc
  deriving DecidableEq

inductive Token where
  | val : os.V → Token
  | res : os.R → Token

abbrev ChanMap := L0.VarMap
abbrev ChanState (os : OpSet) := ChanMap (List (Token os))

variable [PCM os.R] [sem : OpSemantics os]

inductive Label where
  | op : os.Op → List os.V → Label
  | tau : Label

structure ProcState where
  chans : ChanState os
  state : sem.S

abbrev ProcStateM R := StateT (ProcState os) Option R

def ProcStateM.err : ProcStateM os R := StateT.lift none

def ProcStateM.getChans : ProcStateM os (ChanState os) := do
  let config ← get
  return config.chans

def ProcStateM.getState : ProcStateM os sem.S := do
  let config ← get
  return config.state

def ProcStateM.setChans (chans : ChanState os) : ProcStateM os Unit := do
  let config ← get
  set { config with chans := chans }

def ProcStateM.setState (state : sem.S) : ProcStateM os Unit := do
  let config ← get
  set { config with state := state }

def ProcStateM.pop (chan : Chan) : ProcStateM os (Token os) := do
  let chans ← .getChans os
  match chans.get chan with
  | some (v :: vs) => do
    .setChans os (chans.insert chan vs)
    return v
  | _ => ProcStateM.err os

/-- Same as `ProcState.pop`, but expects a value token. -/
def ProcStateM.popValue (chan : Chan) : ProcStateM os os.V := do
  let tok ← ProcStateM.pop os chan
  match tok with
  | .val v => return v
  | .res _ => .err os

/-- Same as `ProcState.pop`, but expects a resource token. -/
def ProcStateM.popRes (chan : Chan) : ProcStateM os os.R := do
  let tok ← ProcStateM.pop os chan
  match tok with
  | .res r => return r
  | .val _ => .err os

def ProcStateM.push (chan : Chan) (v : Token os) : ProcStateM os Unit := do
  let chans ← .getChans os
  match chans.get chan with
  | some vs => .setChans os (chans.insert chan (vs ++ [v]))
  | none => .setChans os (chans.insert chan [v])

def ProcStateM.liftOpM (m : OpM sem.S R) : ProcStateM os R := do
  let config ← get
  match m.run config.state with
  | some (r, newState) => do
    set { config with state := newState }
    return r
  | none => ProcStateM.err os

/-- Interprets an atomic process as a `ProcStateM`. -/
def AtomicProc.interp (p : AtomicProc os) : ProcStateM os (Label os × AtomicProc os) :=
  match p with
  | .op o inChans outChans resInChan resOutChan => do
    -- Read input values and resource
    let inVals ← inChans.mapM (λ inChan => .popValue os inChan)
    let inRes ← .popRes os resInChan
    -- Run the operator
    let outVals ← .liftOpM os (sem.interpOp o inVals)
    -- Write output values and resource
    if outVals.length = outChans.length then
      (outChans.zip outVals).forM (λ (outChan, outVal) =>
        .push os outChan (.val outVal))
      .push os resOutChan (.res (os.specOf o).ensures)
      return (.op o inVals, p)
    else .err os
  | _ => /- TODO: more interpretation -/ sorry

structure Config where
  procs : Finset (AtomicProc os)
  state : ProcState os

def Step (c₁ : Config os) (l : Label os) (c₂ : Config os) : Prop :=
  ∃ p p', p ∈ c₁.procs ∧
    AtomicProc.interp os p = some (l, p') ∧
    c₂ = { c₁ with procs := insert p' (c₁.procs.erase p) }

end Wavelet.L1

/-! Syntax and operational semantics of L1 (second version). -/
namespace Wavelet.L1'

open PCM Op

variable (os : OpSet)
variable [DecidableEq os.Op] [DecidableEq os.V] [DecidableEq os.T] [DecidableEq os.R]

abbrev ProcName := String
abbrev Chan := L0.Var

inductive ChanType [DecidableEq os.T] [DecidableEq os.R] where
  | prim : os.T → ChanType
  | ghost : os.R → ChanType
  deriving DecidableEq

inductive Token [DecidableEq os.V] [DecidableEq os.R] where
  | val : os.V → Token
  | res : os.R → Token
  deriving DecidableEq

inductive AtomicProc [DecidableEq os.Op] [DecidableEq os.V] where
  | op (op : os.Op) (ins : List Chan) (outs : List Chan) (resIn : Chan) (resOut : Chan) : AtomicProc
  | steer (expected : Bool) (decider : Chan) (input : Chan) (output : Chan) : AtomicProc
  | carry (decider : Chan) (input₁ : Chan) (input₂ : Chan) (output : Chan) : AtomicProc
  | merge (decider : Chan) (input₁ : Chan) (input₂ : Chan) (output : Chan) : AtomicProc
  | fork (input : Chan) (output₁ : Chan) (output₂ : Chan) : AtomicProc
  | const (val : os.V) (act : Chan) (output : Chan) : AtomicProc
  | sink (input : Chan) : AtomicProc
  | forward (input : Chan) (output : Chan) : AtomicProc
  deriving DecidableEq

inductive Proc [DecidableEq os.Op] [DecidableEq os.V] [DecidableEq os.T] [DecidableEq os.R] where
  | atom : AtomicProc os → Proc
  | par : Proc → Proc → Proc
  | new : (Chan × ChanType os) → List (Token os) → Proc → Proc
  deriving DecidableEq

abbrev ChanState := Chan → List (Token os)
def ChanState.get (c : Chan) (chans : ChanState os) : List (Token os) := chans c
def ChanState.insert (c : Chan) (ts : List (Token os)) (chans : ChanState os) : ChanState os :=
  λ d => if d = c then ts else chans d

variable [PCM os.R] [sem : OpSemantics os]

inductive Label [DecidableEq os.Op] [DecidableEq os.V] where
  | op : os.Op → List os.V → Label
  | tau : Label
  deriving DecidableEq

structure ProcState where
  chans : ChanState os
  state : sem.S

abbrev ProcStateM := StateT (ProcState os) List

def ProcStateM.err : ProcStateM os R := StateT.lift []

def ProcStateM.getChans : ProcStateM os (ChanState os) := do
  let config ← get
  return config.chans

def ProcStateM.getState : ProcStateM os sem.S := do
  let config ← get
  return config.state

def ProcStateM.setChans (chans : ChanState os) : ProcStateM os Unit := do
  let config ← get
  set { config with chans := chans }

def ProcStateM.setState (state : sem.S) : ProcStateM os Unit := do
  let config ← get
  set { config with state := state }

def ProcStateM.pop (chan : Chan) : ProcStateM os (Token os) := do
  let chans ← .getChans os
  match chans.get os chan with
  | v :: vs => do
    .setChans os (chans.insert os chan vs)
    return v
  | _ => ProcStateM.err os

/-- Same as `ProcState.pop`, but expects a value token. -/
def ProcStateM.popValue (chan : Chan) : ProcStateM os os.V := do
  let tok ← ProcStateM.pop os chan
  match tok with
  | .val v => return v
  | .res _ => .err os

/-- Same as `ProcState.pop`, but expects a resource token. -/
def ProcStateM.popRes (chan : Chan) : ProcStateM os os.R := do
  let tok ← ProcStateM.pop os chan
  match tok with
  | .res r => return r
  | .val _ => .err os

def ProcStateM.push (chan : Chan) (v : Token os) : ProcStateM os Unit := do
  let chans ← .getChans os
  let vs := chans.get os chan
  .setChans os (chans.insert os chan (vs ++ [v]))

def ProcStateM.liftOpM (m : OpM sem.S R) : ProcStateM os R := do
  let config ← get
  match m.run config.state with
  | some (r, newState) => do
    set { config with state := newState }
    return r
  | none => ProcStateM.err os

/-- Steps an atomic process as a `ProcStateM`. -/
def AtomicProc.step (p : AtomicProc os) : ProcStateM os (Label os × AtomicProc os) :=
  match p with
  | .op o inChans outChans resInChan resOutChan => do
    -- Read input values and resource
    let inVals ← inChans.mapM (λ inChan => .popValue os inChan)
    let inRes ← .popRes os resInChan
    -- Run the operator
    let outVals ← .liftOpM os (sem.interpOp o inVals)
    -- Write output values and resource
    if outVals.length = outChans.length then
      (outChans.zip outVals).forM (λ (outChan, outVal) =>
        .push os outChan (.val outVal))
      .push os resOutChan (.res (os.specOf o).ensures)
      return (.op o inVals, p)
    else .err os
  | _ => /- TODO: more interpretation -/ sorry

/-- Steps a process. -/
def Proc.step (p : Proc os) : ProcStateM os (Label os × Proc os) :=
  match p with
  | .atom ap => (ap.step os).map λ (lbl, ap') => (lbl, .atom ap')
  | .par p₁ p₂ => p₁.step <|> p₂.step
  | .new vts buf p => do
      let chans ← .getChans os
      let oldBuf := chans.get os vts.fst
      .setChans os (chans.insert os vts.fst buf)
      let (lbl, p') ← p.step
      -- Restore old buffer
      let chans ← .getChans os
      let newBuf := chans.get os vts.fst
      .setChans os (chans.insert os vts.fst oldBuf)
      return (lbl, .new vts newBuf p')

structure Config where
  proc : Proc os
  state : ProcState os

def Step (c₁ : Config os) (l : Label os) (c₂ : Config os) : Prop :=
  ((l, c₂.proc), c₂.state) ∈ (c₁.proc.step os).run c₁.state

end Wavelet.L1'
