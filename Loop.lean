import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

/-!
Trying a simple version with branching and recursion.
-/

/-
███████╗██╗   ██╗███╗   ██╗████████╗ █████╗ ██╗  ██╗
██╔════╝╚██╗ ██╔╝████╗  ██║╚══██╔══╝██╔══██╗╚██╗██╔╝
███████╗ ╚████╔╝ ██╔██╗ ██║   ██║   ███████║ ╚███╔╝
╚════██║  ╚██╔╝  ██║╚██╗██║   ██║   ██╔══██║ ██╔██╗
███████║   ██║   ██║ ╚████║   ██║   ██║  ██║██╔╝ ██╗
╚══════╝   ╚═╝   ╚═╝  ╚═══╝   ╚═╝   ╚═╝  ╚═╝╚═╝  ╚═╝

We assume a set of operators `Op`, each of which is annotated
with an input arity and an output arity; we also assume a type
of variables `χ`.
-/

universe u

variable (Op : Type u) (χ : Type u)
variable [DecidableEq χ]

class OpArity where
  ι : Op → ℕ
  ω : Op → ℕ

variable [arity : OpArity Op]

inductive Expr : ℕ → ℕ → Type u where
  | ret (vars : Vector χ n) : Expr m n
  | tail (vars : Vector χ m) : Expr m n
  | op (op : Op)
    (args : Vector χ (arity.ι op))
    (bind : Vector χ (arity.ω op))
    (cont : Expr m n) : Expr m n
  | br (cond : χ) (left : Expr m n) (right : Expr m n) : Expr m n

/-- `Fn m n` is a function with `m` inputs and `n` outputs. -/
structure Fn (m : ℕ) (n : ℕ) : Type u where
  params : Vector χ m
  body : Expr Op χ m n
  wf : m > 0 ∧ n > 0

abbrev ChanBuf (V) := χ × List V

def ChanBuf.empty (v : χ) : ChanBuf χ V := (v, [])

def ChanBuf.push (var : χ) (val : V) (buf : ChanBuf χ V) : ChanBuf χ V :=
  if buf.1 = var then (buf.1, buf.2.concat val)
  else (buf.1, buf.2)

def ChanBuf.pop (buf : ChanBuf χ V) : Option (V × ChanBuf χ V) :=
  match buf.2 with
  | [] => none
  | v :: vs => some (v, (buf.1, vs))

inductive AtomicProc (V) where
  | op (op : Op) (inputs : Vector (ChanBuf χ V) (arity.ι op)) (outputs : Vector χ (arity.ω op))
  | steer (decider : ChanBuf χ V) (inputs : Vector (ChanBuf χ V) n) (outputs : Vector χ n)
  | carry (inLoop : Bool)
    (decider : ChanBuf χ V)
    (inputs₁ : Vector (ChanBuf χ V) n) (inputs₂ : Vector (ChanBuf χ V) n)
    (outputs : Vector χ n)
  | merge (decider : ChanBuf χ V)
    (inputs₁ : Vector (ChanBuf χ V) n) (inputs₂ : Vector (ChanBuf χ V) n)
    (outputs : Vector χ n)
  | forward (inputs : Vector (ChanBuf χ V) n) (outputs : Vector χ n)
  | const (c : V) (act : ChanBuf χ V) (outputs : Vector χ n)
  deriving Repr

/-- `Proc _ m n` is a process with `m` inputs and `n` outputs. -/
structure Proc (V) (m : ℕ) (n : ℕ) where
  inputs : Vector χ m
  outputs : Vector (ChanBuf χ V) n
  atoms : List (AtomicProc Op χ V)

/-
███████╗███████╗███╗   ███╗ █████╗ ███╗   ██╗████████╗██╗ ██████╗███████╗
██╔════╝██╔════╝████╗ ████║██╔══██╗████╗  ██║╚══██╔══╝██║██╔════╝██╔════╝
███████╗█████╗  ██╔████╔██║███████║██╔██╗ ██║   ██║   ██║██║     ███████╗
╚════██║██╔══╝  ██║╚██╔╝██║██╔══██║██║╚██╗██║   ██║   ██║██║     ╚════██║
███████║███████╗██║ ╚═╝ ██║██║  ██║██║ ╚████║   ██║   ██║╚██████╗███████║
╚══════╝╚══════╝╚═╝     ╚═╝╚═╝  ╚═╝╚═╝  ╚═══╝   ╚═╝   ╚═╝ ╚═════╝╚══════╝

From this point onwards, we assume that operators in `Op` are interpreted
as state monads.
-/

/-- Interpretation of an operator set as concrete values. -/
class OpInterp (V S : Type u) where
  interp : (op : Op) → Vector V (arity.ι op) → StateT S Option (Vector V (arity.ω op))
  asBool : V → Bool
  -- Some constants used in compilation
  trueVal : V
  falseVal : V
  junkVal : V

variable (V S) [OpInterp Op V S]

/-- Consistent channel naming for the compiler. -/
inductive ChanName where
  | var (base : χ) (count : ℕ) (pathConds : List (Bool × ChanName))
  | merge_cond (chan : ChanName)
  | dest (i : ℕ) (pathConds : List (Bool × ChanName))
  | tail_arg (i : ℕ) (pathConds : List (Bool × ChanName))
  | tail_cond (pathConds : List (Bool × ChanName))
  | final_dest (i : ℕ)
  | final_tail_arg (i : ℕ)
  deriving Repr

/-- State of expression execution. -/
structure ExprState (m n : ℕ) where
  fn : Fn Op χ m n
  vars : χ → Option V
  state : S
  -- Ghost states for the simulation relation
  definedVars : List χ
  pathConds : List (Bool × ChanName χ)

def ExprState.init
  (fn : Fn Op χ m n)
  (state : S)
  (args : Vector V m) : ExprState Op χ V S m n := {
    fn,
    vars := λ v => ((fn.params.zip args).toList.find? (·.1 = v)).map (·.2),
    state,
    definedVars := [],
    pathConds := [],
  }

abbrev ExprStateM m n := StateT (ExprState Op χ V S m n) Option

def ExprStateM.getVar (v : χ) : ExprStateM Op χ V S m n V := do
  match (← get).vars v with
  | some val => return val
  | none => .failure

def ExprStateM.setVar (v : χ) (val : V) : ExprStateM Op χ V S m n PUnit := do
  modify λ s => {
    s with vars := λ x => if x = v then some val else s.vars x
  }

def ExprStateM.tailCall (m : ℕ) (vals : Vector V m) : ExprStateM Op χ V S m n (Fn Op χ m n) := do
  let s ← get
  set (ExprState.init _ _ _ _ s.fn s.state vals)
  return s.fn

def ExprStateM.addDefinedVars (vs : List χ) : ExprStateM Op χ V S m n PUnit := do
  modify λ s => { s with definedVars := s.definedVars ++ vs }

def ExprStateM.addPathCond (b : Bool) (v : χ) : ExprStateM Op χ V S m n PUnit := do
  modify λ s => {
    s with
    pathConds := (b, .var v (s.definedVars.count v) s.pathConds) :: s.pathConds,
  }

def ExprStateM.liftS (s : StateT S Option T) : ExprStateM Op χ V S m n T := do
  let (val, state) ← s.run (← get).state
  modify λ s => { s with state }
  return val

inductive ExprResult (m n : ℕ) where
  | ret (vals : Vector V n)
  | cont (expr : Expr Op χ m n)

def Expr.step : Expr Op χ m n → ExprStateM Op χ V S m n (ExprResult Op χ V m n)
  | .ret vars => do
    let vals ← vars.mapM getVar
    return .ret vals
  | .tail vars => do
    let vals ← vars.mapM getVar
    let fn ← .tailCall _ _ _ _ _ vals
    return .cont fn.body
  | .op o args rets cont => do
    let argVals ← args.mapM getVar
    let retVals ← .liftS _ _ _ _ (OpInterp.interp o argVals)
    (rets.zip retVals).forM λ (v, val) => setVar v val
    .addDefinedVars _ _ _ _ rets.toList
    return .cont cont
  | .br cond left right => do
    let condVal ← getVar cond
    if OpInterp.asBool Op S condVal then
      .addPathCond _ _ _ _ true cond
      return .cont left
    else
      .addPathCond _ _ _ _ false cond
      return .cont right
  where
    getVar := ExprStateM.getVar _ _ _ _
    setVar := ExprStateM.setVar _ _ _ _

structure Expr.Config m n where
  expr : ExprResult Op χ V m n
  estate : ExprState Op χ V S m n

/-- Initialize an expression configuration. -/
def Expr.Config.init
  (fn : Fn Op χ m n)
  (state : S)
  (vars : Vector V m) : Expr.Config Op χ V S m n
  := {
    expr := .cont fn.body,
    estate := ExprState.init _ _ _ _ fn state vars,
  }

/-- Main step relation for expressions. -/
def Expr.Step
  (c c' : Expr.Config Op χ V S m n) : Prop :=
  match c.expr with
  | .ret _ => False
  | .cont expr => some (c'.expr, c'.estate) = (expr.step _ _ _ _).run c.estate

def Expr.StepPlus {m n} := @Relation.TransGen (Expr.Config Op χ V S m n) (Expr.Step Op χ V S)

def Expr.StepStar {m n} := @Relation.ReflTransGen (Expr.Config Op χ V S m n) (Expr.Step Op χ V S)

abbrev ProcStateM := StateT S List

abbrev ChanUpdate := List (χ × V)

def ProcStateM.liftS (s : StateT S Option T) : ProcStateM S T := do
  match s.run (← get) with
  | none => .failure
  | some (val, state) =>
    set state
    return val

def ProcStateM.popBuf
  (buf : ChanBuf χ V) :
  ProcStateM S (V × ChanBuf χ V) :=
  match buf.pop with
  | none => .failure
  | some (v, buf') => return (v, buf')

def ProcStateM.popBufs
  (bufs : Vector (ChanBuf χ V) n) :
  ProcStateM S (Vector V n × Vector (ChanBuf χ V) n) := do
  let vs ← bufs.mapM λ buf => popBuf _ _ _ buf
  return (vs.map Prod.fst, vs.map Prod.snd)

/-- Fire the given atomic process and return the modified process along with channel pushes. -/
def AtomicProc.step :
  AtomicProc Op χ V → ProcStateM S (AtomicProc Op χ V × ChanUpdate χ V)
  | .op o inputs outputs => do
    let (inputVals, inputs') ← .popBufs _ _ _ inputs
    let outputVals ← .liftS _ (OpInterp.interp o inputVals)
    return (.op o inputs' outputs, (outputs.zip outputVals).toList)
  | .steer decider inputs outputs => do
    let (deciderVal, decider') ← .popBuf _ _ _ decider
    let (inputVals, inputs') ← .popBufs _ _ _ inputs
    return (
      .steer decider' inputs' outputs,
      if OpInterp.asBool Op S deciderVal then (outputs.zip inputVals).toList
      else [],
    )
  | .carry inLoop decider inputs₁ inputs₂ outputs => do
    if inLoop then
      let (deciderVal, decider') ← .popBuf _ _ _ decider
      if OpInterp.asBool Op S deciderVal then
        let (inputVals, inputs₂') ← .popBufs _ _ _ inputs₂
        return (.carry true decider' inputs₁ inputs₂' outputs, (outputs.zip inputVals).toList)
      else
        return (.carry false decider' inputs₁ inputs₂ outputs, [])
    else
      let (inputVals, inputs₁') ← .popBufs _ _ _ inputs₁
      return (.carry true decider inputs₁' inputs₂ outputs, (outputs.zip inputVals).toList)
  | .merge decider inputs₁ inputs₂ outputs => do
    let (deciderVal, decider') ← .popBuf _ _ _ decider
    if OpInterp.asBool Op S deciderVal then
      let (inputVals, inputs₁') ← .popBufs _ _ _ inputs₁
      return (.merge decider' inputs₁' inputs₂ outputs, (outputs.zip inputVals).toList)
    else
      let (inputVals, inputs₂') ← .popBufs _ _ _ inputs₂
      return (.merge decider' inputs₁ inputs₂' outputs, (outputs.zip inputVals).toList)
  | .forward inputs outputs => do
    let (inputVals, inputs') ← .popBufs _ _ _ inputs
    return (.forward inputs' outputs, (outputs.zip inputVals).toList)
  | .const c act outputs => do
    let (_, act') ← .popBuf _ _ _ act
    return (.const c act' outputs, outputs.toList.map λ output => (output, c))

/-- Push the given value to input channels with the same variable name. -/
def AtomicProc.push (var : χ) (val : V) : AtomicProc Op χ V → AtomicProc Op χ V
  | .op o inputs outputs => .op o (inputs.map pushVal) outputs
  | .steer decider inputs outputs => .steer (pushVal decider) (inputs.map pushVal) outputs
  | .carry inLoop decider inputs₁ inputs₂ outputs =>
    .carry inLoop (pushVal decider) (inputs₁.map pushVal) (inputs₂.map pushVal) outputs
  | .merge decider inputs₁ inputs₂ outputs =>
    .merge (pushVal decider) (inputs₁.map pushVal) (inputs₂.map pushVal) outputs
  | .forward inputs outputs => .forward (inputs.map pushVal) outputs
  | .const c act outputs => .const c (pushVal act) outputs
  where pushVal := ChanBuf.push _ var val

def Proc.push (var : χ) (val : V) (p : Proc Op χ V m n) : Proc Op χ V m n :=
  {
    p with
    outputs := p.outputs.map (ChanBuf.push _ var val),
    atoms := p.atoms.map (AtomicProc.push _ _ _ var val)
  }

def Proc.pushAll (updates : ChanUpdate χ V) (p : Proc Op χ V m n) : Proc Op χ V m n :=
  updates.foldl (λ p (var, val) => p.push _ _ _ var val) p

/-- Fire the `i`-th atomic process. -/
def Proc.stepAtom (p : Proc Op χ V m n) (i : Fin p.atoms.length) :
  ProcStateM S (Proc Op χ V m n) := do
  let (ap, upd) ← p.atoms[i].step Op χ V S
  let p' := { p with atoms := p.atoms.set i ap }
  let p'' := Proc.pushAll _ _ _ upd p'
  return p''

/-- Non-deterministically choose one atomic process to fire. -/
def Proc.step (p : Proc Op χ V m n) : ProcStateM S (Proc Op χ V m n) := do
  ← (List.finRange p.atoms.length).map λ i => Proc.stepAtom _ _ _ _ p i

structure Proc.Config m n where
  proc : Proc Op χ V m n
  state : S

/-- Initial process configuration. -/
def Proc.Config.init
  (proc : Proc Op χ V m n)
  (state : S)
  (vars : Vector V m) : Proc.Config Op χ V S m n
  := {
    proc := proc.pushAll _ _ _ (proc.inputs.zip vars).toList,
    state,
  }

def Proc.Step (c c' : Proc.Config Op χ V S m n) : Prop :=
  (c'.proc, c'.state) ∈ (c.proc.step Op χ V S).run c.state

def Proc.StepPlus {m n} := @Relation.TransGen (Proc.Config Op χ V S m n) (Proc.Step Op χ V S)

def Proc.StepStar {m n} := @Relation.ReflTransGen (Proc.Config Op χ V S m n) (Proc.Step Op χ V S)

/-
 ██████╗ ██████╗ ███╗   ███╗██████╗ ██╗██╗     ███████╗██████╗
██╔════╝██╔═══██╗████╗ ████║██╔══██╗██║██║     ██╔════╝██╔══██╗
██║     ██║   ██║██╔████╔██║██████╔╝██║██║     █████╗  ██████╔╝
██║     ██║   ██║██║╚██╔╝██║██╔═══╝ ██║██║     ██╔══╝  ██╔══██╗
╚██████╗╚██████╔╝██║ ╚═╝ ██║██║     ██║███████╗███████╗██║  ██║
 ╚═════╝ ╚═════╝ ╚═╝     ╚═╝╚═╝     ╚═╝╚══════╝╚══════╝╚═╝  ╚═╝

We define compilers from `Expr` and `Fn` to `Proc`.
-/

/--
Compiles an expression to a list of atomic processes, with
exactly `m + n + 1` outputs, where `m` is the number of parameters
of the encompassing function, `n` is the number of return values,
and the extra output is a Boolean indicating whether the expression
chooses to perform a tail call (with `m` arguments) or return
`n` final values.
-/
def Expr.compile
  (wf : m > 0 ∧ n > 0) -- Additional well-formedness condition
  (definedVars : List χ)
  (pathConds : List (Bool × ChanName χ))
  : Expr Op χ m n → List (AtomicProc Op (ChanName χ) V)
  | .ret vars =>
    let chans := vars.map liveVar
    let act := chans[0] -- Use the first return value as an activation signal
    [
      .forward chans retChans,
      -- No tail recursion, so we send junk values for the tail arguments
      -- and send `false` on the tail condition channel.
      .const (OpInterp.junkVal Op S) act tailArgs,
      .const (OpInterp.falseVal Op S) act #v[.tail_cond pathConds]
    ]
  | .tail vars =>
    let chans := vars.map liveVar
    let act := chans[0]
    [
      .const (OpInterp.junkVal Op S) act retChans,
      .forward chans tailArgs,
      .const (OpInterp.trueVal Op S) act #v[.tail_cond pathConds]
    ]
  | .op o args rets cont =>
    let inputChans := args.map liveVar
    let (definedVars', outputChans) := newVars rets
    (.op o inputChans outputChans) :: compile wf definedVars' pathConds cont
  | .br cond left right => do
    let condChan := liveVar cond
    let leftConds := (true, condChan.1) :: pathConds
    let rightConds := (false, condChan.1) :: pathConds
    let leftComp := compile wf definedVars leftConds left
    let rightComp := compile wf definedVars rightConds right
    let allVars := definedVars.eraseDups.toArray.toVector
    [
      -- Steer all live variables
      .steer condChan
        (allVars.map λ v => .empty _ (.var v (definedVars.count v) pathConds))
        (allVars.map λ v => .var v (definedVars.count v) leftConds),
      -- Forward the condition again to the merge
      -- (extra forward for a simpler simulation relation)
      .forward #v[condChan] #v[.merge_cond condChan.1],
    ] ++ leftComp ++ rightComp ++ [
      -- Merges at the end so that we can maintain a simpler DAG property.
      -- Merge tail call conditions
      .merge (.empty _ (.merge_cond condChan.1))
        #v[.empty _ (.tail_cond leftConds)]
        #v[.empty _ (.tail_cond rightConds)]
        #v[.tail_cond pathConds],
      -- Merge return values of both branches
      .merge (.empty _ (.merge_cond condChan.1))
        ((Vector.range n).mapIdx λ i _ => .empty _ (.dest i leftConds))
        ((Vector.range n).mapIdx λ i _ => .empty _ (.dest i rightConds))
        ((Vector.range n).mapIdx λ i _ => .dest i pathConds),
      -- Merge tail call arguments of both branches
      .merge (.empty _ (.merge_cond condChan.1))
        ((Vector.range m).mapIdx λ i _ => .empty _ (.tail_arg i leftConds))
        ((Vector.range m).mapIdx λ i _ => .empty _ (.tail_arg i rightConds))
        ((Vector.range m).mapIdx λ i _ => .tail_arg i pathConds),
    ]
  where
    liveVar v := .empty _ (.var v (definedVars.count v) pathConds)
    retChans := (Vector.range n).mapIdx λ i _ => .dest i pathConds
    tailArgs := (Vector.range m).mapIdx λ i _ => .tail_arg i pathConds
    newVars {k} (vs : Vector χ k) : List χ × Vector (ChanName χ) k :=
      (
        definedVars ++ vs.toList,
        vs.map λ v => .var v (definedVars.count v + 1) pathConds
      )

/--
Compiles a function to a process with `m` inputs and `n` outputs.

Most of the compiled process should be a DAG, except for the back
edges of channels with the name `.tail_cond []` or `.tail_arg i []`.
-/
def Fn.compile
  (fn : Fn Op χ m n) : Proc Op (ChanName χ) V m n
  :=
  let bodyComp := fn.body.compile Op χ V S fn.wf fn.params.toList []
  {
    inputs := fn.params.map λ v => .var v 0 [],
    outputs := (Vector.range n).map λ i => .empty _ (.final_tail_arg i),
    atoms := [
      -- A carry gate to merge initial values and tail call arguments
      .carry
        false
        (.empty _ (.tail_cond []))
        (fn.params.map λ v => .empty _ (.var v 0 []))
        ((Vector.range m).map λ i => .empty _ (.final_tail_arg i))
        (fn.params.map λ v => .var v 1 []),
    ] ++ bodyComp ++ [
      -- If tail condition is true, discard the junk return values
      .steer
        (.empty _ (.tail_cond []))
        ((Vector.range n).map λ i => .empty _ (.dest i []))
        ((Vector.range n).map λ i => .final_dest i),
      -- If tail condition is false, discard the junk tail arguments
      .steer
        (.empty _ (.tail_cond []))
        ((Vector.range m).map λ i => .empty _ (.tail_arg i []))
        ((Vector.range m).map λ i => .final_tail_arg i),
    ]
  }
