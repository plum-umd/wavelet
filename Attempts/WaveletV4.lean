import Mathlib.Data.List.Basic

/-! A formulation of partial commutative monoids. -/
class PCM (C : Type u) where
  add : C → C → C
  zero : C
  valid : C → Prop
  eq : C → C → Prop

/-! Notations and axioms for PCM. -/
namespace Wavelet.PCM

infixl:60 " ⬝ " => PCM.add
infix:50 " ≡ " => PCM.eq
prefix:40 "✓ " => PCM.valid

def disjoint {C : Type u} [PCM C] (a b : C) : Prop := ✓ a ⬝ b

/-- TODO: Implement some type class for partial order. -/
def le {C : Type u} [PCM C] (a b : C) : Prop := ∃ c, b ≡ a ⬝ c

def framePreserving {C : Type u} [PCM C] (a b : C) : Prop :=
  ∀ c, ✓ a ⬝ c → ✓ b ⬝ c

infix:50 " ⊥ " => disjoint
infix:50 " ≤ " => le
infix:50 " ⟹ " => framePreserving

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

/-! Defines syntax and semantics of operator sets. -/
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

variable (χ : Type) [DecidableEq χ] -- Variable names
variable (os : OpSet)

abbrev Vars := List χ
abbrev FnName := String

inductive Expr where
  | vars : Vars χ → Expr
  | tail : Vars χ → Expr
  | let_fn : (boundVars : Vars χ) → FnName → (args : Vars χ) → Expr → Expr
  | let_op : (boundVars : Vars χ) → os.Op → (args : Vars χ) → Expr → Expr
  | let_const : χ → os.V → Expr → Expr
  | branch : χ → Expr → Expr → Expr

structure FnDef where
  name : FnName
  ins : List (χ × os.T)
  outTys : List os.T
  requires : os.R
  ensures : os.R
  body : Expr χ os

/-- A utility type for partial maps from `Var`. -/
abbrev VarMap (T : Type u) := χ → Option T

def VarMap.get (x : χ) (vars : VarMap χ T) : Option T := vars x

def VarMap.insert (x : χ) (t : T) (vars : VarMap χ T) : VarMap χ T :=
  λ y => if y = x then some t else vars y

def VarMap.insertOption (x : χ) (t : Option T) (vars : VarMap χ T) : VarMap χ T :=
  λ y => if y = x then t else vars y

def VarMap.remove (x : χ) (vars : VarMap χ T): VarMap χ T :=
  λ y => if y = x then none else vars y

def VarMap.fromList (vs : List (χ × T)) : VarMap χ T :=
  λ x => (vs.find? (λ (k, _) => k = x)).map Prod.snd

def VarMap.insertVars (vs : List (χ × T)) (vars : VarMap χ T) : VarMap χ T :=
  λ x => (VarMap.fromList χ vs).get χ x <|> vars x

end Wavelet.L0

/-! Typing rules for L0. -/
namespace Wavelet.L0

open PCM Op

variable (χ : Type) [DecidableEq χ] -- Variable names

/--
For convenience, new `FnDef`s are inserted at the front,
i.e., `FnDef`s at the front can only call those at the back.
-/
abbrev FnCtx os := List (FnDef χ os)

structure Ctx (os : OpSet) where
  self : FnDef χ os
  fns : FnCtx χ os
  vars : VarMap χ os.T
  res : os.R

def FnCtx.intersect {os : OpSet} (fns₁ fns₂ : FnCtx χ os) : FnCtx χ os :=
  fns₁.filter (λ fn₁ => fns₂.any (λ fn₂ => fn₁.name = fn₂.name))

def FnCtx.getFn {os : OpSet} (name : FnName) (fns : FnCtx χ os) : Option (FnDef χ os × FnCtx χ os) :=
  match fns with
  | [] => none
  | fn :: fns' =>
    if fn.name = name then
      some (fn, fns')
    else
      FnCtx.getFn name fns'

def Ctx.WellTypedVars {os : OpSet} (vs : Vars χ) (tys : List os.T) (Γ : Ctx χ os) : Prop :=
  List.Forall₂ (λ v t => Γ.vars.get χ v = some t) vs tys

def Ctx.getFn {os : OpSet} (name : FnName) (Γ : Ctx χ os) : Option (FnDef χ os) := Prod.fst <$> Γ.fns.getFn χ name

def Ctx.updateRes {os : OpSet} (r : os.R) (Γ : Ctx χ os) : Ctx χ os :=
  { Γ with res := r }

/-- Typing rules -/
inductive Expr.WellTyped {os : OpSet} [PCM os.R] : Ctx χ os → Expr χ os → Ctx χ os → List os.T → Prop where
  /-- Well-typed variables -/
  | wt_vars :
    Γ.WellTypedVars χ vs tys →
    Expr.WellTyped Γ (.vars vs) Γ tys
  /-- Well-typed recursive tail call -/
  | wt_tail :
    Γ.WellTypedVars χ args (Prod.snd <$> Γ.self.ins) →
    Γ.self.requires ⬝ frame ≡ Γ.res →
    Expr.WellTyped
      Γ (.tail args)
      (Γ.updateRes χ (Γ.self.ensures ⬝ frame)) Γ.self.outTys
  /-- Well-typed let fn call -/
  | wt_let_fn :
    Γ.getFn χ fnName = some fn →
    Γ.WellTypedVars χ args (Prod.snd <$> fn.ins) →
    fn.requires ⬝ frame ≡ Γ.res →
    boundVars.length = fn.outTys.length →
    Expr.WellTyped {
      Γ with
      res := fn.ensures ⬝ frame,
      vars := Γ.vars.insertVars χ (boundVars.zip fn.outTys)
    } cont Γ' tys →
    Expr.WellTyped Γ (.let_fn boundVars fnName args cont) Γ' tys
  /-- Well-typed let op call -/
  | wt_let_op :
    Γ.WellTypedVars χ args (os.specOf op).inTys →
    (os.specOf op).requires ⬝ frame ≡ Γ.res →
    boundVars.length = (os.specOf op).outTys.length →
    Expr.WellTyped {
      Γ with
      res := (os.specOf op).ensures ⬝ frame,
      vars := Γ.vars.insertVars χ (boundVars.zip (os.specOf op).outTys)
    } cont Γ' tys →
    Expr.WellTyped Γ (.let_op boundVars op args cont) Γ' tys
  /-- Well-typed let constant -/
  | wt_let_const :
    Expr.WellTyped {
      Γ with
      vars := Γ.vars.insert χ var (os.typeOf val)
    } cont Γ' tys →
    Expr.WellTyped Γ (.let_const var val cont) Γ' tys
  /-- Well-typed branching -/
  | wt_branch :
    -- Condition is well-typed
    Γ.vars.get χ x = some t →
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
        fns := Γ₁.fns.intersect χ Γ₂.fns,
        res := res'
      } tys

def FnDef.WellTyped {os : OpSet} [PCM os.R] (fns : FnCtx χ os) (fn : FnDef χ os) : Prop :=
  ∃ vars' res',
    Expr.WellTyped χ
      { self := fn, fns, vars := VarMap.fromList χ fn.ins, res := fn.requires }
      fn.body
      { self := fn, fns, vars := vars', res := res' }
      fn.outTys ∧
    res' ≤ fn.ensures

inductive FnCtx.WellTyped {os : OpSet} [PCM os.R] : FnCtx χ os → Prop where
  | wt_nil : FnCtx.WellTyped []
  | wt_cons :
    FnCtx.WellTyped fns →
    FnDef.WellTyped χ fns fn →
    FnCtx.WellTyped (fn :: fns)

end Wavelet.L0

namespace Wavelet.ITree

/-- An inductive version of interaction trees with an explicit fixpoint constructor. -/
inductive FixTree (E : Type u → Type v) : Type w → Type (max (u + 1) v (w + 2)) where
  | ret : R → FixTree E R
  | vis : E A → (A → FixTree E R) → FixTree E R
  | fix {A B : Type w} : (A → FixTree E (A ⊕ B)) → A → (B → FixTree E R) → FixTree E R

def FixTree.bind {A B : Type u} (t : FixTree E A) (f : A → FixTree E B) : FixTree E B :=
  match t with
  | .ret r => f r
  | .vis e k => .vis e (λ x => (k x).bind f)
  | .fix m i k => .fix m i (λ x => (k x).bind f)

instance : Monad (FixTree E) where
  pure := .ret
  bind := .bind

/-- Types of next actions allowed in any `FixTree`. -/
inductive FixTreeUnfolded (E : Type u → Type v) : Type w → Type (max (u + 1) v (w + 2)) where
  | ret : R → FixTreeUnfolded E R
  | tau : FixTree E R → FixTreeUnfolded E R
  | vis : E A → (A → FixTree E R) → FixTreeUnfolded E R

/--
Destructs/unfolds a `FixTree` to get `FixTreeShape`.
TODO: figure out why this is ok.
-/
def FixTree.destruct (t : FixTree E R) : FixTreeUnfolded E R :=
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

end Wavelet.ITree

/-! An small-step operational semantics of L0. -/
namespace Wavelet.L0

open PCM Op

variable (χ : Type) [DecidableEq χ] -- Variable names
variable (os : OpSet) [PCM os.R]
variable [sem : OpSemantics os]

inductive Label where
  | op : os.Op → List os.V → Label
  | tau : Label

/-- A saved stack frame. -/
structure Frame where
  locals : VarMap χ os.V
  fn : FnDef χ os
  contVars : Vars χ
  contExpr : Expr χ os

structure ExprState where
  fns : FnCtx χ os
  stack : List (Frame χ os)
  locals : VarMap χ os.V
  fn : FnDef χ os
  state : sem.S

abbrev ExprStateM := StateT (ExprState χ os) Option

def ExprStateM.err : ExprStateM χ os R := StateT.lift Option.none

def ExprStateM.getLocals : ExprStateM χ os (VarMap χ os.V) := ExprState.locals <$> get

def ExprStateM.setLocals (locals : VarMap χ os.V) : ExprStateM χ os Unit :=
  modify λ config => { config with locals := locals }

def ExprStateM.curFn : ExprStateM χ os (FnDef χ os) := ExprState.fn <$> get

def ExprStateM.getLocal (var : χ) : ExprStateM χ os (os.V) := do
  let locals ← .getLocals χ os
  match locals.get χ var with
  | some v => return v
  | none => .err χ os

def ExprStateM.setLocal (var : χ) (val : os.V) : ExprStateM χ os Unit := do
  let locals ← .getLocals χ os
  .setLocals χ os (locals.insert χ var val)

/-- Restores the next stack frame if it exists. -/
def ExprStateM.restoreStack : ExprStateM χ os (Option (Frame χ os)) := do
  let config ← get
  match config.stack with
  | [] => return none
  | f :: rest => do
    set { config with stack := rest, locals := f.locals, fn := f.fn }
    return f

/-- Saves the current stack frame. -/
def ExprStateM.saveStack (contVars : Vars χ) (contExpr : Expr χ os) : ExprStateM χ os Unit := do
  let config ← get
  let frame := { locals := config.locals, fn := config.fn, contVars, contExpr }
  set { config with stack := frame :: config.stack }

def ExprStateM.liftOpM (m : OpM sem.S R) : ExprStateM χ os R := do
  let config ← get
  match m.run config.state with
  | some (r, newState) => do
    set { config with state := newState }
    return r
  | none => .err χ os

/--
Finds the function in the context with the given name,
and then removes the prefix of `ExprState.fns` that does
not match the name.
-/
def ExprStateM.getFn (name : FnName) : ExprStateM χ os (FnDef χ os) := do
  let config ← get
  match config.fns.getFn χ name with
  | some (fn, fns') => do
    set { config with fns := fns' }
    return fn
  | none => .err χ os

inductive ExprResult where
  | final : List os.V → ExprResult
  | cont : Expr χ os → ExprResult

def Expr.step : Expr χ os → ExprStateM χ os (Label os × ExprResult χ os)
  | .vars vs => do
    let vals ← vs.mapM (.getLocal χ os)
    match ← .restoreStack χ os with
    | none => return (.tau, .final vals)
    | some f =>
      if f.contVars.length ≠ vals.length then .err χ os
      (f.contVars.zip vals).forM (λ (v, val) => .setLocal χ os v val)
      return (.tau, .cont f.contExpr)
  | .tail args => do
    let fn ← .curFn χ os
    let vals ← args.mapM (.getLocal χ os)
    if fn.ins.length ≠ vals.length then .err χ os
    -- Initialize new locals for the tail call
    let locals := VarMap.fromList χ (List.zip (fn.ins.map Prod.fst) vals)
    .setLocals χ os locals
    return (.tau, .cont fn.body)
  | .let_fn boundVars fnName args cont => do
    let fn ← .getFn χ os fnName
    let argVals ← args.mapM (.getLocal χ os)
    if fn.ins.length ≠ argVals.length then .err χ os
    let locals := VarMap.fromList χ (List.zip (fn.ins.map Prod.fst) argVals)
    .saveStack χ os boundVars cont
    .setLocals χ os locals
    return (.tau, .cont fn.body)
  | .let_op boundVars op args cont => do
    let argVals ← args.mapM (.getLocal χ os)
    let retVals ← .liftOpM χ os (sem.interpOp op argVals)
    if boundVars.length ≠ retVals.length then .err χ os
    (boundVars.zip retVals).forM (λ (v, val) => .setLocal χ os v val)
    return (.op op argVals, .cont cont)
  | .let_const var val cont => do
    .setLocal χ os var val
    return (.tau, .cont cont)
  | .branch cond left right => do
    let condVal ← .getLocal χ os cond
    if let some b := os.asBool condVal then
      if b then
        return (.tau, .cont left)
      else
        return (.tau, .cont right)
    else
      .err χ os

structure Config where
  res : ExprResult χ os
  estate : ExprState χ os

inductive Step : Config χ os → Label os → Config χ os → Prop where
  | step (l : Label os) :
    (expr.step χ os).run estate = some ((l, res), estate') →
    Step { res := .cont expr, estate } l { res, estate := estate' }

end Wavelet.L0

/-! Syntax and operational semantics of L1. -/
namespace Wavelet.L1

open PCM Op

variable (χ : Type) [DecidableEq χ] -- Channel names
variable (os : OpSet)

abbrev ProcName := String

inductive ChanType where
  | prim : os.T → ChanType
  | ghost : os.R → ChanType

inductive Token where
  | val : os.V → Token
  | res : os.R → Token

inductive AtomicProc where
  | op (op : os.Op) (inputs : List χ) (outputs : List χ) (resInput : χ) (resOutput : χ) : AtomicProc
  -- | steer (flavor : Bool) (decider : χ) (input : χ) (output : χ) : AtomicProc
  -- | carry (init : Bool) (flavor : Bool) (decider : χ) (input₁ : χ) (input₂ : χ) (output : χ) : AtomicProc
  -- | merge (decider : χ) (input₁ : χ) (input₂ : χ) (output : χ) : AtomicProc
  | steer (flavor : Bool) (decider : χ) (inputs : List χ) (outputs : List χ) : AtomicProc
  | carry (init : Bool) (flavor : Bool) (decider : χ) (inputs₁ : List χ) (inputs₂ : List χ) (output : List χ) : AtomicProc
  | merge (decider : χ) (inputs₁ : List χ) (inputs₂ : List χ) (output : List χ) : AtomicProc
  | fork (input : χ) (output₁ : χ) (output₂ : χ) : AtomicProc
  | const (val : os.V) (act : χ) (output : χ) : AtomicProc
  | sink (input : χ) : AtomicProc
  | forward (input : χ) (output : χ) : AtomicProc

-- mutual

inductive Proc where
  | atom : AtomicProc χ os → Proc
  | par : Proc → Proc → Proc
  | new : (chan : χ) → (typ : ChanType os) → (init : List (Token os)) → Proc → Proc
  -- | graph :
  --   (inputs : List χ) → (outputs : List χ) →
  --   (inputs' : List (χ × ChanType os)) →
  --   (outputs' : List (χ × ChanType os)) →
  --   Proc → Proc

-- structure Graph where
--   ins : List (χ × ChanType os)
--   outs : List (χ × ChanType os)
--   proc : Proc

-- end -- mutual

abbrev ChanState := χ → List (Token os)

def ChanState.empty : ChanState χ os := λ _ => []

def ChanState.get (c : χ) (chans : ChanState χ os) : List (Token os) := chans c

def ChanState.insert (c : χ) (ts : List (Token os)) (chans : ChanState χ os) : ChanState χ os :=
  λ d => if d = c then ts else chans d

inductive Label where
  | op : os.Op → List os.V → Label
  | tau : Label

variable [PCM os.R] [sem : OpSemantics os]

structure ProcState where
  chans : ChanState χ os
  state : sem.S

abbrev ProcStateM := StateT (ProcState χ os) List

def ProcStateM.err : ProcStateM χ os R := StateT.lift []

def ProcStateM.getChans : ProcStateM χ os (ChanState χ os) := do
  let config ← get
  return config.chans

def ProcStateM.getChan (chan : χ) : ProcStateM χ os (List (Token os)) := do
  let config ← get
  return config.chans.get χ os chan

def ProcStateM.getState : ProcStateM χ os sem.S := do
  let config ← get
  return config.state

def ProcStateM.setChans (chans : ChanState χ os) : ProcStateM χ os Unit := do
  let config ← get
  set { config with chans := chans }

def ProcStateM.setChan (chan : χ) (toks : List (Token os)) : ProcStateM χ os Unit := do
  let config ← get
  set { config with chans := config.chans.insert χ os chan toks }

def ProcStateM.setState (state : sem.S) : ProcStateM χ os Unit := do
  let config ← get
  set { config with state := state }

def ProcStateM.pop (chan : χ) : ProcStateM χ os (Token os) := do
  let chans ← .getChans χ os
  match chans.get χ os chan with
  | v :: vs => do
    .setChans χ os (chans.insert χ os chan vs)
    return v
  | _ => ProcStateM.err χ os

/-- Same as `ProcState.pop`, but expects a value token. -/
def ProcStateM.popValue (chan : χ) : ProcStateM χ os os.V := do
  let tok ← ProcStateM.pop χ os chan
  match tok with
  | .val v => return v
  | .res _ => .err χ os

/-- Same as `ProcStateM.popValue`, but in addition expects a Boolean. -/
def ProcStateM.popBool (chan : χ) : ProcStateM χ os Bool := do
  let v ← .popValue χ os chan
  if let some b := os.asBool v then
    return b
  else
    .err χ os

/-- Same as `ProcState.pop`, but expects a resource token. -/
def ProcStateM.popRes (chan : χ) : ProcStateM χ os os.R := do
  let tok ← ProcStateM.pop χ os chan
  match tok with
  | .res r => return r
  | .val _ => .err χ os

def ProcStateM.popMany (chans : List χ) : ProcStateM χ os (List (Token os)) :=
  chans.mapM (λ chan => .pop χ os chan)

def ProcStateM.popManyValues (chans : List χ) : ProcStateM χ os (List os.V) :=
  chans.mapM (λ chan => .popValue χ os chan)

def ProcStateM.push (chan : χ) (v : Token os) : ProcStateM χ os Unit := do
  let chans ← .getChans χ os
  let vs := chans.get χ os chan
  .setChans χ os (chans.insert χ os chan (vs ++ [v]))

def ProcStateM.pushMany (chans : List χ) (toks : List (Token os)) : ProcStateM χ os Unit := do
  if chans.length = toks.length then
    (chans.zip toks).forM λ (c, v) => .push χ os c v
  else
    .err χ os

def ProcStateM.pushManyValues (chans : List χ) (vals : List os.V) : ProcStateM χ os Unit := do
  if chans.length = vals.length then
    (chans.zip vals).forM λ (c, v) => .push χ os c (.val v)
  else
    .err χ os

def ProcStateM.liftOpM (m : OpM sem.S R) : ProcStateM χ os R := do
  let config ← get
  match m.run config.state with
  | some (r, newState) => do
    set { config with state := newState }
    return r
  | none => .err χ os

/-- Steps an atomic process as a `ProcStateM`. -/
def AtomicProc.step (p : AtomicProc χ os) : ProcStateM χ os (Label os × AtomicProc χ os) :=
  match p with
  | .op o inputs outputs resInput resOutput => do
    -- Read input values and resource
    let inVals ← .popManyValues χ os inputs
    let _ ← .popRes χ os resInput -- resource is not used in semantics
    -- Run the operator
    let outVals ← .liftOpM χ os (sem.interpOp o inVals)
    -- Write output values and resource
    .pushManyValues χ os outputs outVals
    .push χ os resOutput (.res (os.specOf o).ensures)
    return (.op o inVals, p)
  | .steer flavor decider inputs outputs => do
    let b ← .popBool χ os decider
    let toks ← inputs.mapM (λ input => .pop χ os input)
    if b = flavor then
      .pushMany χ os outputs toks
    return (.tau, p)
  | .carry init flavor decider inputs₁ inputs₂ outputs => do
    if init then
      .popMany χ os inputs₁ >>= .pushMany χ os outputs
      return (.tau, .carry false flavor decider inputs₁ inputs₂ outputs)
    else
      let b ← .popBool χ os decider
      if b = flavor then
        .popMany χ os inputs₂ >>= .pushMany χ os outputs
        return (.tau, .carry false flavor decider inputs₁ inputs₂ outputs)
      else
        return (.tau, .carry true flavor decider inputs₁ inputs₂ outputs)
  | .merge decider inputs₁ inputs₂ outputs => do
    let b ← .popBool χ os decider
    if b then
      .popMany χ os inputs₁ >>= .pushMany χ os outputs
    else
      .popMany χ os inputs₂ >>= .pushMany χ os outputs
    return (.tau, p)
  | .fork input output₁ output₂ => do
    let v ← .pop χ os input
    .push χ os output₁ v
    .push χ os output₂ v
    return (.tau, p)
  | .const val act output => do
    let _ ← .pop χ os act
    .push χ os output (.val val)
    return (.tau, p)
  | .sink input => do
    let _ ← .pop χ os input
    return (.tau, p)
  | .forward input output => do
    .pop χ os input >>= .push χ os output
    return (.tau, p)

/-- Defines the semantics of one step of a `Proc`. -/
def Proc.step (p : Proc χ os) : ProcStateM χ os (Label os × Proc χ os) :=
  match p with
  | .atom ap => (ap.step χ os).map λ (lbl, ap') => (lbl, .atom ap')
  | .par p₁ p₂ => p₁.step <|> p₂.step
  | .new chan ty buf p => do
    let chans ← .getChans χ os
    let oldBuf := chans.get χ os chan
    .setChans χ os (chans.insert χ os chan buf)
    let (lbl, p') ← p.step
    -- Restore old buffer
    let chans ← .getChans χ os
    let newBuf := chans.get χ os chan
    .setChans χ os (chans.insert χ os chan oldBuf)
    return (lbl, .new chan ty newBuf p')
  -- | .graph inputs outputs g => do
  --   let oldChans ← .getChans χ os
  --   .setChans χ os (.empty χ os)
  --   if inputs.length ≠ g.ins.length ∨ outputs.length ≠ g.outs.length then
  --     .err χ os
  --   -- In the new channel state, replace the input and output channels
  --   (inputs.zip g.ins).forM λ (input, (gInput, _)) =>
  --     .setChan χ os gInput (oldChans.get χ os input)
  --   (outputs.zip g.outs).forM λ (output, (gOutput, _)) =>
  --     .setChan χ os gOutput (oldChans.get χ os output)
  --   -- Step the inner process
  --   let (lbl, proc') ← g.proc.step
  --   -- Restore the old channel state, except for channels bound by the graph
  --   let chans ← .getChans χ os
  --   .setChans χ os (oldChans)
  --   (inputs.zip g.ins).forM λ (input, (gInput, _)) =>
  --     .setChan χ os input (chans.get χ os gInput)
  --   (outputs.zip g.outs).forM λ (output, (gOutput, _)) =>
  --     .setChan χ os output (chans.get χ os gOutput)
  --   return (lbl, .graph inputs outputs { g with proc := proc' })

structure Config where
  proc : Proc χ os
  pstate : ProcState χ os

def Step (c₁ : Config χ os) (l : Label os) (c₂ : Config χ os) : Prop :=
  ((l, c₂.proc), c₂.pstate) ∈ (c₁.proc.step χ os).run c₁.pstate

theorem step_tau_label_preserves_state
  (hs : Step χ os c₁ .tau c₂) :
  c₁.pstate.state = c₂.pstate.state := sorry

theorem step_op_label_changes_state
  (hs : Step χ os c₁ (.op o vs) c₂) :
  ∃ vs, (sem.interpOp o vs).run c₁.pstate.state = some (vs, c₂.pstate.state) := by
  simp only [Step, StateT.run] at hs
  cases h : c₁.proc with
  | atom ap =>
    simp only [h, Proc.step, StateT.map, List.pure_def, List.bind_eq_flatMap, List.mem_flatMap,
      List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, Prod.exists,
      exists_eq_right_right'] at hs
    cases ap with
    | op o' inChans outChans resInChan resOutChan =>
      have ⟨l, p', hs'⟩ := hs
      simp [AtomicProc.step] at hs'
      sorry
    | _ => sorry
  | par p₁ p₂ => sorry
  | new chan ty buf p => sorry
  -- | graph ins outs g => sorry

end Wavelet.L1

/-! A compiler from L0 programs to L1 processes. -/
namespace Wavelet.Compile

open PCM Op

variable (os : OpSet)

/-- Defined this way to help defining the simulation relation. -/
inductive Chan χ where
  | var : χ → (fnName : L0.FnName) → (shadow : ℕ) → (copy : ℕ) → Chan χ

structure CompileCtx χ where
  /-- Current function being compiled -/
  self : L0.FnDef χ os
  /-- Map from L0 variables to channel names -/
  chans : L0.VarMap χ (Chan χ)
  /-- Channel for activation signals -/
  actChan : Chan χ
  /-- Channel to indicate whether we have a tail recursion -/
  tailFlag : Chan χ
  /-- Channels to output results -/
  outChans : List (Chan χ)
  /-- Channels to output tail call arguments -/
  tailChans : List (Chan χ)

def compileExpr
  (fns : L0.FnCtx χ os)
  (ctx : CompileCtx os χ)
  : L0.Expr χ os → L1.Proc (Chan χ) os :=
  sorry

end Wavelet.Compile

/-
TODOs and questions:
- Well-typed L1 processes have the same semantics on fair and complete traces.
- Well-typed L0 programs compile to well-typed L1 processes.
- L0 program is simulated by the compiled L1 process.
- Futher ghost resource erasure and equivalence (maybe together with L1-level rewrites).
-/
