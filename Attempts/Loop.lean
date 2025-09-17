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

/-- Some static, non-typing constraints on expressions. -/
inductive Expr.WellFormed : Expr Op χ n m → Prop where
  | wf_ret : WellFormed (.ret vars)
  | wf_tail : WellFormed (.tail vars)
  | wf_op :
    rets.toList.Nodup →
    WellFormed cont →
    WellFormed (.op o args rets cont)
  | wf_br :
    WellFormed left →
    WellFormed right →
    WellFormed (.br c left right)

/-- `Fn m n` is a function with `m` inputs and `n` outputs. -/
structure Fn (m : ℕ) (n : ℕ) : Type u where
  params : Vector χ m
  body : Expr Op χ m n
  wf : m > 0 ∧ n > 0 ∧
    params.toList.Nodup ∧
    Expr.WellFormed _ _ body

def Fn.NonEmptyIO (fn : Fn Op χ m n) : m > 0 ∧ n > 0 :=
  ⟨fn.wf.1, fn.wf.2.1⟩

def Fn.WellFormedBody (fn : Fn Op χ m n) : Expr.WellFormed _ _ fn.body :=
  fn.wf.2.2.2

abbrev ChanBuf (V) := χ × List V

def ChanBuf.empty (v : χ) : ChanBuf χ V := (v, [])

def ChanBuf.push (var : χ) (val : V) (buf : ChanBuf χ V) : ChanBuf χ V :=
  if buf.1 = var then (buf.1, buf.2.concat val)
  else (buf.1, buf.2)

def ChanBuf.pop (buf : ChanBuf χ V) : Option (V × ChanBuf χ V) :=
  match buf.2 with
  | [] => none
  | v :: vs => some (v, (buf.1, vs))

inductive AtomicProc V where
  | op (op : Op) (inputs : Vector (ChanBuf χ V) (arity.ι op)) (outputs : Vector χ (arity.ω op))
  | steer (flavor : Bool) (decider : ChanBuf χ V) (inputs : Vector (ChanBuf χ V) n) (outputs : Vector χ n)
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

abbrev AtomicProcs V := List (AtomicProc Op χ V)

/-- `Proc _ m n` is a process with `m` inputs and `n` outputs. -/
structure Proc V (m : ℕ) (n : ℕ) where
  inputs : Vector χ m
  outputs : Vector (ChanBuf χ V) n
  atoms : AtomicProcs Op χ V

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

variable (V S) [instInterp : OpInterp Op V S]

/-- Consistent channel naming for the compiler. -/
inductive ChanName where
  | var (base : χ) (count : ℕ) (pathConds : List (Bool × ChanName))
  -- Only sent during branching
  | merge_cond (chan : ChanName)
  -- Only sent during ret/tail
  | dest (i : ℕ) (pathConds : List (Bool × ChanName))
  -- Only sent during ret/tail
  | tail_arg (i : ℕ) (pathConds : List (Bool × ChanName))
  -- Only sent during ret/tail
  | tail_cond (pathConds : List (Bool × ChanName))
  -- Only sent during the final steers
  | final_dest (i : ℕ)
  | final_tail_arg (i : ℕ)
  deriving Repr

/-- TODO: should be auto-derived -/
instance : DecidableEq (ChanName χ) := sorry

abbrev VarMap := χ → Option V

def VarMap.insertVars
  (vars : Vector χ n)
  (vals : Vector V n)
  (m : VarMap χ V) : VarMap χ V :=
  λ v => ((vars.zip vals).toList.find? (·.1 = v)).map (·.2) <|> m v

def VarMap.getVar (v : χ) (m : VarMap χ V) : Option V := m v

def VarMap.getVars
  (vars : Vector χ n)
  (m : VarMap χ V) : Option (Vector V n) :=
  vars.mapM m

/-- State of expression execution. -/
structure ExprState (m n : ℕ) where
  fn : Fn Op χ m n
  vars : VarMap χ V
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
    definedVars := fn.params.toList,
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
  (args : Vector V m) : Expr.Config Op χ V S m n
  := {
    expr := .cont fn.body,
    estate := ExprState.init _ _ _ _ fn state args,
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
  | .steer flavor decider inputs outputs => do
    let (deciderVal, decider') ← .popBuf _ _ _ decider
    let (inputVals, inputs') ← .popBufs _ _ _ inputs
    return (
      .steer flavor decider' inputs' outputs,
      if OpInterp.asBool Op S deciderVal = flavor then (outputs.zip inputVals).toList
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

/-- Pushes all relevant channel updates. -/
def ChanBuf.pushAll
  (updates : ChanUpdate χ V)
  (buf : ChanBuf χ V) : ChanBuf χ V :=
  updates.foldl (λ buf (var, val) => ChanBuf.push _ var val buf) buf

def AtomicProc.pushAll (updates : ChanUpdate χ V) : AtomicProc Op χ V → AtomicProc Op χ V
  | .op o inputs outputs => .op o (inputs.map pushVal) outputs
  | .steer flavor decider inputs outputs => .steer flavor (pushVal decider) (inputs.map pushVal) outputs
  | .carry inLoop decider inputs₁ inputs₂ outputs =>
    .carry inLoop (pushVal decider) (inputs₁.map pushVal) (inputs₂.map pushVal) outputs
  | .merge decider inputs₁ inputs₂ outputs =>
    .merge (pushVal decider) (inputs₁.map pushVal) (inputs₂.map pushVal) outputs
  | .forward inputs outputs => .forward (inputs.map pushVal) outputs
  | .const c act outputs => .const c (pushVal act) outputs
  where pushVal := ChanBuf.pushAll _ _ updates

def AtomicProcs.pushAll
  (updates : ChanUpdate χ V)
  (aps : AtomicProcs Op χ V) :
  AtomicProcs Op χ V :=
  aps.map (AtomicProc.pushAll _ _ _ updates)

def Proc.pushAll (updates : ChanUpdate χ V) (p : Proc Op χ V m n) : Proc Op χ V m n :=
  { p with
    outputs := p.outputs.map (ChanBuf.pushAll _ _ updates),
    atoms := AtomicProcs.pushAll _ _ _ updates p.atoms }

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
  : Expr Op χ m n → AtomicProcs Op (ChanName χ) V
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
  | .br cond left right =>
    let condChan := liveVar cond
    let leftConds := (true, condChan.1) :: pathConds
    let rightConds := (false, condChan.1) :: pathConds
    let leftComp := compile wf definedVars leftConds left
    let rightComp := compile wf definedVars rightConds right
    let allVars := definedVars.eraseDups.toArray.toVector
    [
      -- Steer all live variables
      .steer true condChan
        (allVars.map λ v => empty (.var v (definedVars.count v) pathConds))
        (allVars.map λ v => .var v (definedVars.count v) leftConds),
      .steer false condChan
        (allVars.map λ v => empty (.var v (definedVars.count v) pathConds))
        (allVars.map λ v => .var v (definedVars.count v) rightConds),
      -- Forward the condition again to the merge
      -- (extra forward for a simpler simulation relation)
      .forward #v[condChan] #v[.merge_cond condChan.1],
    ] ++ leftComp ++ rightComp ++ [
      -- Merge tail call conditions, return values and tail call arguments
      -- from both branches. This is done at the end so that we can keep
      -- the graph as "acyclic" as possible.
      brMerge m n condChan.1 [] pathConds
    ]
  where
    empty := ChanBuf.empty _
    liveVar v := empty (.var v (definedVars.count v) pathConds)
    retChans := (Vector.range n).map λ i => .dest i pathConds
    tailArgs := (Vector.range m).map λ i => .tail_arg i pathConds
    newVars {k} (vs : Vector χ k) : List χ × Vector (ChanName χ) k :=
      (
        definedVars ++ vs.toList,
        vs.map λ v => .var v (definedVars.count v + 1) pathConds
      )
    brMerge m n condName condBuf pathConds :=
      let leftConds := (true, condName) :: pathConds
      let rightConds := (false, condName) :: pathConds
      let leftResults := #v[empty (.tail_cond leftConds)] ++
        ((Vector.range n).map λ i => empty (.dest i leftConds)) ++
        ((Vector.range m).map λ i => empty (.tail_arg i leftConds))
      let rightResults := #v[empty (.tail_cond rightConds)] ++
        ((Vector.range n).map λ i => empty (.dest i rightConds)) ++
        ((Vector.range m).map λ i => empty (.tail_arg i rightConds))
      let results := #v[ChanName.tail_cond pathConds] ++
        ((Vector.range n).map λ i => ChanName.dest i pathConds) ++
        ((Vector.range m).map λ i => ChanName.tail_arg i pathConds)
      .merge (.merge_cond condName, condBuf)
        leftResults
        rightResults
        results

/--
Compiles a function to a process with `m` inputs and `n` outputs.

Most of the compiled process should be a DAG, except for the back
edges of channels with the name `.tail_cond []` or `.tail_arg i []`.
-/
def Fn.compile
  (fn : Fn Op χ m n) : Proc Op (ChanName χ) V m n
  :=
  {
    inputs := fn.params.map λ v => .var v 0 [],
    outputs := (Vector.range n).map λ i => .empty _ (.final_tail_arg i),
    atoms := initCarry :: (bodyComp ++ resultSteers m n)
  }
  where
    -- A carry gate to merge initial values and tail call arguments
    initCarry :=
      .carry false
        (.empty _ (.tail_cond []))
        (fn.params.map λ v => .empty _ (.var v 0 []))
        ((Vector.range m).map λ i => .empty _ (.final_tail_arg i))
        (fn.params.map λ v => .var v 1 [])
    bodyComp := fn.body.compile Op χ V S fn.NonEmptyIO fn.params.toList []
    resultSteers m n := [
      -- If tail condition is true, discard the junk return values
      .steer false
        (.empty _ (.tail_cond []))
        ((Vector.range n).map λ i => .empty _ (.dest i []))
        ((Vector.range n).map λ i => .final_dest i),
      -- If tail condition is false, discard the junk tail arguments
      .steer true
        (.empty _ (.tail_cond []))
        ((Vector.range m).map λ i => .empty _ (.tail_arg i []))
        ((Vector.range m).map λ i => .final_tail_arg i),
    ]

def Refines
  {T : Type v} {S : Type w}
  (c₁ : T) (c₂ : S)
  (R : T → S → Prop)
  (Step₁ : T → T → Prop)
  (Step₂ : S → S → Prop) :=
  R c₁ c₂ ∧
  (∀ c₁ c₂ c₁',
    R c₁ c₂ →
    Step₁ c₁ c₁' →
    ∃ c₂', Step₂ c₂ c₂' ∧ R c₁' c₂')

def Expr.RefinesProc
  [DecidableEq χ₁] [DecidableEq χ₂]
  (c₁ : Expr.Config Op χ₁ V S m n)
  (c₂ : Proc.Config Op χ₂ V S m n)
  (R : Expr.Config Op χ₁ V S m n → Proc.Config Op χ₂ V S m n → Prop) : Prop :=
  Refines c₁ c₂ R (Expr.Step Op χ₁ V S) (Proc.StepPlus Op χ₂ V S)

def AtomicProc.inputs (ap : AtomicProc Op χ V) : List (ChanBuf χ V) :=
  match ap with
  | .op _ inputs _ => inputs.toList
  | .steer _ decider inputs _ => [decider] ++ inputs.toList
  | .carry _ decider input₁ input₂ _ => [decider] ++ input₁.toList ++ input₂.toList
  | .merge decider input₁ input₂ _ => [decider] ++ input₁.toList ++ input₂.toList
  | .forward inputs _ => inputs.toList
  | .const _ act _ => [act]

def AtomicProc.outputs (ap : AtomicProc Op χ V) : List χ :=
  match ap with
  | .op _ _ outputs => outputs.toList
  | .steer _ _ _ outputs => outputs.toList
  | .carry _ _ _ _ outputs => outputs.toList
  | .merge _ _ _ outputs => outputs.toList
  | .forward _ outputs => outputs.toList
  | .const _ _ outputs => outputs.toList

def AtomicProc.HasInput (ap : AtomicProc Op χ V) (v : χ) : Prop :=
  ∃ inp ∈ ap.inputs, inp.1 = v

def AtomicProc.HasInputWithBuf (ap : AtomicProc Op χ V) (v : χ) (buf : List V) : Prop :=
  ∃ inp ∈ ap.inputs, inp = (v, buf)

def AtomicProc.HasEmptyInputs (ap : AtomicProc Op χ V) : Prop :=
  ∀ inp ∈ ap.inputs, inp.2 = []

def ChanBuf.MatchModBuffer (buf₁ buf₂ : ChanBuf χ V) : Prop := buf₁.1 = buf₂.1

def AtomicProc.MatchModBuffers : AtomicProc Op χ V → AtomicProc Op χ V → Prop
  | .op o₁ inputs₁ outputs₁, .op o₂ inputs₂ outputs₂ =>
    o₁ = o₂ ∧
    List.Forall₂ MatchBuf inputs₁.toList inputs₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | .steer flavor₁ decider₁ inputs₁ outputs₁, .steer flavor₂ decider₂ inputs₂ outputs₂ =>
    flavor₁ = flavor₂ ∧
    decider₁.1 = decider₂.1 ∧
    List.Forall₂ MatchBuf inputs₁.toList inputs₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | .carry inLoop₁ decider₁ inputs₁₁ inputs₁₂ outputs₁,
    .carry inLoop₂ decider₂ inputs₂₁ inputs₂₂ outputs₂ =>
    inLoop₁ = inLoop₂ ∧
    decider₁.1 = decider₂.1 ∧
    List.Forall₂ MatchBuf inputs₁₁.toList inputs₂₁.toList ∧
    List.Forall₂ MatchBuf inputs₁₂.toList inputs₂₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | .merge decider₁ inputs₁₁ inputs₁₂ outputs₁,
    .merge decider₂ inputs₂₁ inputs₂₂ outputs₂ =>
    decider₁.1 = decider₂.1 ∧
    List.Forall₂ MatchBuf inputs₁₁.toList inputs₂₁.toList ∧
    List.Forall₂ MatchBuf inputs₁₂.toList inputs₂₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | .forward inputs₁ outputs₁, .forward inputs₂ outputs₂ =>
    List.Forall₂ MatchBuf inputs₁.toList inputs₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | .const c₁ act₁ outputs₁, .const c₂ act₂ outputs₂ =>
    c₁ = c₂ ∧ act₁.1 = act₂.1 ∧
    outputs₁.toList = outputs₂.toList
  | _, _ => False
  where
    @[simp]
    MatchBuf := ChanBuf.MatchModBuffer _ _

def AtomicProcs.MatchModBuffers (aps₁ aps₂ : AtomicProcs Op χ V) : Prop :=
  List.Forall₂ (AtomicProc.MatchModBuffers Op χ V) aps₁ aps₂

def AtomicProcs.IsDAG (aps : AtomicProcs Op χ V) : Prop :=
  ∀ i j, (hi : i < aps.length) → (hj : j ≤ i) →
    ∀ output ∈ aps[i].outputs, ¬ aps[j].HasInput Op χ V output

def AtomicProcs.HasEmptyInputs (aps : AtomicProcs Op χ V) : Prop :=
  ∀ ap ∈ aps, ap.HasEmptyInputs Op χ V

/-- Checks if the channel name is a variable and it has
a different suffix than the given path condition. -/
def ChanName.HasDiffPathSuffix (pathConds : List (Bool × ChanName χ)) (name : ChanName χ) : Prop :=
  match name with
  | .var _ _ pathConds' => ∀ ext, ext ++ pathConds ≠ pathConds'
  | _ => True

def AtomicProc.HasDiffPathSuffix (pathConds : List (Bool × ChanName χ)) (ap : AtomicProc Op (ChanName χ) V) : Prop :=
  ∀ inp ∈ ap.inputs, inp.1.HasDiffPathSuffix _ pathConds

def AtomicProcs.HasDiffPathSuffix (pathConds : List (Bool × ChanName χ)) (aps : AtomicProcs Op (ChanName χ) V) : Prop :=
  ∀ ap ∈ aps, ap.HasDiffPathSuffix _ _ _ pathConds

def SimR (ec : Expr.Config Op χ V S m n) (pc : Proc.Config Op (ChanName χ) V S m n) : Prop :=
  ec.estate.state = pc.state ∧
  -- The process matches the compiled function in shape
  AtomicProcs.MatchModBuffers _ _ _ pc.proc.atoms (Fn.compile Op χ V S ec.estate.fn).atoms ∧
  ∃ (rest : AtomicProcs Op (ChanName χ) V)
    (carryInLoop : Bool)
    (carryDecider : ChanBuf (ChanName χ) V)
    (carryInputs₁ carryInputs₂ : Vector (ChanBuf (ChanName χ) V) m)
    (carryOutputs : Vector (ChanName χ) m)
    (ctxLeft ctxCurrent ctxRight : AtomicProcs Op (ChanName χ) V),
    -- The processes form a DAG if we remove the first carry operator
    pc.proc.atoms = (.carry carryInLoop carryDecider carryInputs₁ carryInputs₂ carryOutputs) :: rest ∧
    rest.IsDAG _ _ _ ∧
    -- States of the first carry gate
    (¬ carryInLoop → ∀ input ∈ carryInputs₁, ∃ var val, input = (.var var 0 [], [val])) ∧
    (carryInLoop → ∀ input ∈ carryInputs₁, input.2 = []) ∧
    -- The processes can be split into three fragments
    rest = ctxLeft ++ ctxCurrent ++ ctxRight ∧
    ctxLeft.HasEmptyInputs _ _ _ ∧
    -- If we have reached the end of execution, nothing else should be executable
    (∀ vals, ec.expr = .ret vals →
      ctxCurrent = [] ∧
      ctxRight = [] ∧
      -- Same return value in the proc side
      List.Forall₂ (λ v (_, buf) => buf = [v])
        vals.toList pc.proc.outputs.toList) ∧
    -- If we still have a continuation
    (∀ expr, ec.expr = .cont expr →
      expr.WellFormed ∧
      -- The current fragment corresponds to the compilation results
      AtomicProcs.MatchModBuffers _ _ _
        ctxCurrent
        (expr.compile Op χ V S ec.estate.fn.NonEmptyIO ec.estate.definedVars ec.estate.pathConds) ∧
      -- Some constraints about live variables
      (∀ ap ∈ ctxCurrent, ∀ inp ∈ ap.inputs,
        -- Check if the channel name corresponds to a live variable
        -- in the current branch
        let IsLiveVar (name : ChanName χ) val := ∃ var,
          ec.estate.vars var = some val ∧
          name = .var var (ec.estate.definedVars.count var) ec.estate.pathConds
        -- If it's a live var, the channel buffer should have the corresponding value
        (∀ val, IsLiveVar inp.1 val → inp.2 = [val]) ∧
        -- Otherwise it's empty.
        ((∀ val, ¬ IsLiveVar inp.1 val) → inp.2 = [])) ∧
      -- The remaining processes in `ctxRight` should be of the form
      --
      --   `p₁ ... pₘ || merge || p'₁ ... p'ₖ || merge || ...`
      --
      -- i.e., a sequence of processes interspersed with consecutive
      -- chunks of n merge nodes.
      -- Furthermore, all processes other than these merges should
      -- have empty input buffers, and the merges will have exactly
      -- one Boolean in the decider buffers corresponding to the
      -- branching decision.
      (∃ (chunks : List (AtomicProcs Op (ChanName χ) V × AtomicProc Op (ChanName χ) V))
        (tail : AtomicProcs Op (ChanName χ) V),
        ctxRight = (joinM (chunks.map (λ (l, r) => l ++ [r]))) ++ tail ∧
        -- The first half chunks and the tail have empty inputs
        (∀ chunk₁ chunk₂, (chunk₁, chunk₂) ∈ chunks →
          chunk₁.HasEmptyInputs _ _ _ ∧
          chunk₁.HasDiffPathSuffix _ _ _ ec.estate.pathConds) ∧
        tail.HasEmptyInputs _ _ _ ∧
        tail.HasDiffPathSuffix _ _ _ ec.estate.pathConds ∧
        -- The second half chunk corresponds exactly to the merge nodes
        -- generated along the branches marked in the current `pathConds`.
        List.Forall₂
          (λ (_, merge) i =>
            let (b, cond) := ec.estate.pathConds[i]
            let prevPathConds := ec.estate.pathConds.drop (i + 1)
            ∃ v,
              OpInterp.asBool Op S v = b ∧
              -- Same as the original merge gate, except with the corresponding
              -- branching decision in the decider buffer.
              merge = Expr.compile.brMerge Op _ _ m n cond [v] prevPathConds)
          chunks
          (Vector.finRange ec.estate.pathConds.length).toList))

/-
Invariants?

- Equal global states
- Proc is a DAG except for the back edges of the first carry
- The first carry gate has either
  - inLoop = false, and its first input set non-empty, and second input set empty
  - inLoop = true, and all of its input buffers empty
- Proc matches the following shapes
  - proc matches fn.compile modulo buffers
  - proc = [carry] ++ A ++ B ++ C ++ [steer₁, steer₂], where
    - A is a list of atoms with empty buffers
    - B matches expr.compile modulo buffers
    - C is a list of atoms, interspersed with a list of merges
      with the same length as pathConds. Each merge has the decider
      channel set with one value.
-/

theorem aps_match_mod_bufs_refl
  {aps : AtomicProcs Op χ V} :
  AtomicProcs.MatchModBuffers Op χ V aps aps := sorry

theorem aps_push_preserves_shape
  {aps : AtomicProcs Op χ V}
  {upd : ChanUpdate χ V} :
  AtomicProcs.MatchModBuffers Op χ V (AtomicProcs.pushAll Op χ V upd aps) aps := sorry

theorem aps_push_preserves_dag
  {aps : AtomicProcs Op χ V}
  {upd : ChanUpdate χ V}
  (hdag : AtomicProcs.IsDAG Op _ V aps) :
  AtomicProcs.IsDAG Op _ V (AtomicProcs.pushAll Op χ V upd aps) := sorry

theorem aps_push_commutes_tail
  {aps : AtomicProcs Op χ V}
  {upd : ChanUpdate χ V} :
  (AtomicProcs.pushAll Op χ V upd aps).tail
    = AtomicProcs.pushAll Op χ V upd aps.tail := sorry

theorem aps_push_commutes_append
  {aps₁ aps₂ : AtomicProcs Op χ V}
  {upd : ChanUpdate χ V} :
  (AtomicProcs.pushAll Op χ V upd (aps₁ ++ aps₂))
    = (AtomicProcs.pushAll Op χ V upd aps₁) ++ (AtomicProcs.pushAll Op χ V upd aps₂) := sorry

/-- The result of compilation should be a DAG except for the first carry process. -/
theorem fn_compile_dag
  {fn : Fn Op χ m n} :
  AtomicProcs.IsDAG Op _ V ((Fn.compile Op χ V S fn).atoms.tail) := sorry

/-- Initial configs satisfy the simulation relation. -/
theorem sim_init_config
  (f : Fn Op χ m n)
  (p : Proc Op (ChanName χ) V m n)
  (hcomp : f.compile Op χ V S = p)
  (s : S)
  (args : Vector V m) :
  SimR _ _ _ _
    (Expr.Config.init _ _ _ _ f s args)
    (Proc.Config.init _ _ _ _ p s args) := by
  simp only [← hcomp]
  and_intros
  · rfl
  · apply aps_push_preserves_shape
  · generalize hinitUpd : ((Fn.compile Op χ V S f).inputs.zip args).toList = initUpd
    exists
      (Proc.pushAll Op _ _ initUpd p).atoms.tail,
      false,
      (.empty _ (.tail_cond [])),
      (f.params.map λ v => (ChanBuf.empty _ (.var v 0 [])).pushAll _ _ initUpd),
      ((Vector.range m).map λ i => .empty _ (.final_tail_arg i)),
      (f.params.map λ v => .var v 1 []),
      [],
      AtomicProcs.pushAll Op _ _ initUpd (Fn.compile.bodyComp Op χ V S f),
      AtomicProcs.pushAll Op _ _ initUpd (Fn.compile.resultSteers Op χ V m n)
    and_intros
    · simp [Proc.Config.init, Proc.pushAll, aps_push_commutes_tail, ← hcomp]
      cases h : (Fn.compile Op χ V S f).atoms with
      | nil => simp [Fn.compile] at h
      | cons carry rest =>
        simp [AtomicProcs.pushAll, List.tail, hinitUpd]
        -- TODO: Reason about carry substitution
        simp [Fn.compile, Fn.compile.initCarry] at h
        simp only [← h.1, AtomicProc.pushAll, AtomicProc.pushAll.pushVal]
        congr 1
        · sorry
        · sorry
        · sorry
    · simp [Proc.pushAll, aps_push_commutes_tail, ← hcomp]
      apply aps_push_preserves_dag
      apply fn_compile_dag
    · simp
      -- Some facts about push
      sorry
    · simp
    · simp only [Proc.pushAll, aps_push_commutes_tail, ← hcomp, Fn.compile]
      simp [List.tail, aps_push_commutes_append]
    · simp [AtomicProcs.HasEmptyInputs]
    · simp [Expr.Config.init]
    · intros expr hexpr
      simp [Expr.Config.init] at hexpr
      simp only [← hexpr]
      and_intros
      · exact f.WellFormedBody
      · simp only [Fn.compile.bodyComp, Expr.Config.init, ExprState.init]
        apply aps_push_preserves_shape
      · intros ap hap inp hinp
        constructor
        · intros val hval
          have ⟨var, hvar_lookup, hvar_name⟩ := hval
          simp [Expr.Config.init, ExprState.init] at hvar_lookup
          sorry
        · sorry
      · exists [], AtomicProcs.pushAll Op _ _ initUpd (Fn.compile.resultSteers Op χ V m n)
        simp [joinM]
        and_intros
        · -- TODO: reason about steer pushes
          sorry
        · -- TODO: reason about HasDiffPathSuffix
          sorry
        · constructor

theorem aps_match_symmetric
  {aps aps' : AtomicProcs Op χ V}
  (hmatch : AtomicProcs.MatchModBuffers Op χ V aps aps') :
  AtomicProcs.MatchModBuffers Op χ V aps' aps := sorry

theorem aps_match_implies_exists_ap_match
  (aps aps' : AtomicProcs Op χ V)
  (ap : AtomicProc Op χ V)
  (hmatch : AtomicProcs.MatchModBuffers Op χ V aps aps')
  (hmem : ap ∈ aps) :
  ∃ ap' ∈ aps', AtomicProc.MatchModBuffers Op χ V ap ap'
  := sorry

def ChanBuf.HasSingletonBufs (bufs : Vector (ChanBuf χ V) n) (vals : Vector V n) : Prop :=
  List.Forall₂ (λ (_, buf) v => buf = [v]) bufs.toList vals.toList

def ChanBuf.clearBufs (bufs : Vector (ChanBuf χ V) n) : Vector (ChanBuf χ V) n :=
  bufs.map (λ (var, _) => (var, []))

-- /-- Alternative semantics of an op atom. -/
-- theorem proc_step_op
--   (pc : Proc.Config Op (ChanName χ) V S m n)
--   (inputVals : Vector V (OpArity.ι o))
--   (hinputs : ChanBuf.HasSingletonBufs _ _ inputs inputVals)
--   (hmem : pc.proc.atoms = left ++ [AtomicProc.op o inputs outputs] ++ right)
--   (hop : (OpInterp.interp o inputVals).run pc.state = some (outputVals, state')) :
--   ∃ pc',
--     let updates := (outputs.zip outputVals).toList
--     Proc.Step _ _ _ _ pc pc' ∧
--     pc'.state = state' ∧
--     pc'.proc.outputs = pc.proc.outputs.map (ChanBuf.pushAll _ _ updates) ∧
--     pc'.proc.atoms = AtomicProcs.pushAll _ _ _ updates
--       (left ++ [AtomicProc.op o (ChanBuf.clearBufs _ _ inputs) outputs] ++ right)
--   := sorry

/-- Alternative operational semantics. -/
inductive Expr.Step' : Expr.Config Op χ V S m n → Expr.Config Op χ V S m n → Prop where
  | step_op {args : Vector χ (OpArity.ι o)}
    (hinputs : vars.getVars _ _ args = some inputVals)
    (hop : (instInterp.interp o inputVals).run state = some (outputVals, state')) :
    Step'
      {
        expr := .cont (.op o args rets cont),
        estate := {
          fn, vars,
          definedVars := definedVars,
          pathConds := pathConds,
          state,
        },
      }
      {
        expr := .cont cont,
        estate := {
          fn,
          vars := vars.insertVars _ _ rets outputVals,
          definedVars := definedVars ++ rets.toList,
          pathConds := pathConds,
          state := state',
        },
      }

def ChanBuf.popBufs (bufs : Vector (ChanBuf χ V) n) : Option (Vector V n × Vector (ChanBuf χ V) n) := do
  let res ← bufs.mapM λ (var, buf) => match buf with
    | [] => none
    | v :: buf => some (v, (var, buf))
  return (res.map Prod.fst, res.map Prod.snd)

inductive Proc.Step' : Proc.Config Op χ V S m n → Proc.Config Op χ V S m n → Prop where
  | step_op
    {inputs : Vector (ChanBuf χ V) (OpArity.ι o)} {outputs}
    (hinputs : ChanBuf.popBufs _ _ inputs = some (inputVals, inputs'))
    (hop : (instInterp.interp o inputVals).run state = some (outputVals, state')) :
    Step'
      {
        proc := {
          inputs := procInputs,
          outputs := procOutputs,
          atoms := ctxLeft ++ [AtomicProc.op o inputs outputs] ++ ctxRight
        },
        state,
      }
      {
        proc := {
          inputs := procInputs,
          outputs := procOutputs.map (.pushAll _ _ (outputs.zip outputVals).toList),
          atoms :=
            .pushAll _ _ _ (outputs.zip outputVals).toList
            (ctxLeft ++ [AtomicProc.op o inputs' outputs] ++ ctxRight)
        },
        state := state',
      }

theorem expr_step_to_step' :
  Expr.Step Op χ V S ec ec' ↔ Expr.Step' Op χ V S ec ec' := by
  sorry

theorem proc_step_to_step' :
  Proc.StepPlus Op χ V S pc pc' ↔ Proc.Step' Op χ V S pc pc' := by
  sorry

theorem sim_step
  (ec ec' : Expr.Config Op χ V S m n)
  (pc : Proc.Config Op (ChanName χ) V S m n)
  (hsim : SimR _ _ _ _ ec pc)
  (hstep : Expr.Step Op χ V S ec ec') :
  ∃ pc',
    Proc.StepPlus Op (ChanName χ) V S pc pc' ∧
    SimR _ _ _ _ ec' pc' := by
  have ⟨
    heq_state,
    hmatch_fn,
    ⟨
      rest,
      carryInLoop,
      carryDecider,
      carryInputs₁,
      carryInputs₂,
      carryOutputs,
      ctxLeft,
      ctxCurrent,
      ctxRight,
      hatoms,
      hdag,
      hcarry_false,
      hcarry_true,
      hrest,
      hempty_ctxLeft,
      hret,
      hcont,
    ⟩,
  ⟩ := hsim
  cases hexpr : ec.expr with
  | ret vals => simp only [Expr.Step, hexpr] at hstep
  | cont expr =>
    -- simp only [Expr.Step, hexpr] at hstep
    have ⟨
      hwf_expr,
      hmatch_ctxCurrent,
      hlive_vars,
      hctxRight,
    ⟩ := hcont expr hexpr
    cases expr with
    | ret vars =>
      simp only [Expr.Step, hexpr, Expr.step] at hstep
      simp [Expr.compile] at hmatch_ctxCurrent
      sorry
    | tail => sorry
    | op o args bind cont =>
      simp only [Expr.Step] at hstep
      simp only [Expr.Step, hexpr, Expr.step] at hstep
      simp [Expr.compile] at hmatch_ctxCurrent
      -- generalize hap :
      --   AtomicProc.op o
      --     (Vector.map (Expr.compile.liveVar χ V ec.estate.definedVars ec.estate.pathConds) args)
      --     (Expr.compile.newVars χ ec.estate.definedVars ec.estate.pathConds bind).snd
      --   = ap
      -- simp only [hap] at hmatch_ctxCurrent
      have ⟨ap, hap_mem, hap_match⟩ := aps_match_implies_exists_ap_match
        _ _ _ _ _ _
        (aps_match_symmetric _ _ _ hmatch_ctxCurrent)
        List.mem_cons_self
      simp [AtomicProc.MatchModBuffers] at hap_match
      cases ap <;> simp at hap_match
      rename_i o' inputs outputs
      have ⟨heq_o, hap_match_inputs, hap_match_outputs⟩ := hap_match
      have hmem_ap : AtomicProc.op o' inputs outputs ∈ pc.proc.atoms := by
        simp only [hrest] at hatoms
        simp [hatoms]
        right; left
        assumption
      -- TODO: from hlive_vars

      have hinputs : ∀ input ∈ inputs, ∃ var val,
        some val = ec.estate.vars var ∧
        input = (.var var (ec.estate.definedVars.count var) ec.estate.pathConds, [val]) := sorry

      -- TODO: from `hinputs'` and `hmem_ap'`,
      --       show that we can run the atomic process
      --       and substitute the result to the remainder of `ctxCurrent`.
      --       - `ctxLeft` remain unchanged due to DAG structure
      --       - `ctxRight` remain unchanged due to ??? (different pathConds)
      -- TODO: show that the result preserves the relational invariant...
      sorry
    | br => sorry

theorem compile_refines
  (f : Fn Op χ m n)
  (p : Proc Op (ChanName χ) V m n)
  (hcomp : f.compile Op χ V S = p)
  (s : S)
  (args : Vector V m) :
  Refines
    (Expr.Config.init _ _ _ _ f s args)
    (Proc.Config.init _ _ _ _ p s args)
    (SimR _ _ _ _)
    (Expr.Step Op χ V S)
    (Proc.StepPlus Op (ChanName χ) V S) := by
  constructor
  · apply sim_init_config
    exact hcomp
  · intros ec pc ec' hstep
    apply sim_step _ _ _ _ ec ec'
    exact hstep
