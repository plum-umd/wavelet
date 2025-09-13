import Mathlib.Data.List.Basic

/-!
Trying a simple version without function calls or recursion.
-/

variable
  (Op : Type u) -- Type of operators
  (χ : Type u) -- Type of variables

class OpArity where
  ι : Op → ℕ
  ω : Op → ℕ

variable [arity : OpArity Op]

inductive Expr : ℕ → Type u where
  | ret (vars : Vector χ n) : Expr n
  | op (op : Op)
    (args : Vector χ (arity.ι op))
    (rets : Vector χ (arity.ω op))
    (cont : Expr n) : Expr n
  | br (cond : χ) (left : Expr n) (right : Expr n) : Expr n

abbrev InputBuf (V) := χ × List V

def InputBuf.empty (v : χ) : InputBuf χ V := (v, [])

inductive AtomicProc (V) where
  | op (op : Op) (inputs : Vector (InputBuf χ V) (arity.ι op)) (outputs : Vector χ (arity.ω op))
  | steer (decider : InputBuf χ V) (input : InputBuf χ V) (output : χ)
  | merge (decider : InputBuf χ V) (input₁ : InputBuf χ V) (input₂ : InputBuf χ V) (output : χ)
  | forward (inputs : Vector (InputBuf χ V) n) (outputs : Vector χ n)
  deriving Repr

abbrev Proc (V) := List (AtomicProc Op χ V)

inductive ChanName where
  | var (base : χ) (shadow : ℕ) (pathConds : List (Bool × ChanName))
  | dest (i : ℕ) (pathConds : List (Bool × ChanName))
  deriving Repr

def compile
  [DecidableEq χ]
  (definedVars : List χ)
  (pathConds : List (Bool × ChanName χ))
  : Expr Op χ n → Option (Proc Op (ChanName χ) V)
  | .ret vars => do
    let chans := vars.map curVar
    let dests := (Vector.range n).mapIdx λ i _ => .dest i pathConds
    return [.forward chans dests]
  | .op op args rets cont => do
    let inputChans := args.map curVar
    let (definedVars', outputChans) := newVars definedVars rets
    return (.op op inputChans outputChans) ::
           (← compile definedVars' pathConds cont)
  | .br cond left right => do
    let condChan := curVar cond
    let leftConds := (true, condChan.1) :: pathConds
    let rightConds := (false, condChan.1) :: pathConds
    let leftComp ← compile definedVars leftConds left
    let rightComp ← compile definedVars rightConds right
    -- Merge results from the two branches
    let merges :=
      (List.range n).mapIdx λ i _ =>
        .merge condChan
          (.empty _ (.dest i leftConds))
          (.empty _ (.dest i rightConds))
          (.dest i pathConds)
    -- Filter variables to the branch body based on the branch condition
    let steers :=
      definedVars.eraseDups.map λ v =>
        .steer condChan
          (.empty _ (.var v (definedVars.count v) pathConds))
          (.var v (definedVars.count v) leftConds)
    return steers ++ merges ++ leftComp ++ rightComp
  where
    /-- Generates the current channel name of the given variable name. -/
    curVar v := .empty _ (.var v (definedVars.count v) pathConds)
    /--
    Defines new variables while maintaining a list of defined variables.
    `vs` may contain duplicates.
    -/
    newVars {m : ℕ} (definedVars : List χ) (vs : Vector χ m) : List χ × Vector (ChanName χ) m :=
      match m with
      | 0 => (definedVars, #v[])
      | m' + 1 =>
        let v := vs[0]
        let definedVars' := v :: definedVars
        let name := ChanName.var v (definedVars'.count v) pathConds
        let (definedVars'', rest) := newVars definedVars' vs.tail
        (definedVars'', ⟨(name :: rest.toList).toArray, by simp⟩)

def compileTop [DecidableEq χ] : Expr Op χ n → Option (Proc Op (ChanName χ) V) :=
  compile Op χ [] []

section Semantics

/-- Interpretation of an operator set as concrete values. -/
class OpInterp (V S : Type u) where
  interp : (op : Op) → Vector V (arity.ι op) → StateT S Option (Vector V (arity.ω op))
  asBool : V → Bool

variable (V S) [OpInterp Op V S]

inductive Label where
  | op (op : Op) (args : Vector V (arity.ι op))
  | tau
  deriving Repr

structure ExprState where
  vars : χ → Option V
  state : S

abbrev ExprStateM := StateT (ExprState χ V S) Option

def ExprStateM.getVar (v : χ) : ExprStateM χ V S V := do
  match (← get).vars v with
  | some val => return val
  | none => .failure

def ExprStateM.setVar [DecidableEq χ] (v : χ) (val : V) : ExprStateM χ V S PUnit := do
  modify λ s => {
    s with vars := λ x => if x = v then some val else s.vars x
  }

def ExprStateM.liftS (s : StateT S Option T) : ExprStateM χ V S T := do
  let (val, state) ← s.run (← get).state
  modify λ s => { s with state }
  return val

inductive ExprResult (n : ℕ) where
  | ret (vals : Vector V n)
  | cont (expr : Expr Op χ n)

def Expr.step [DecidableEq χ] : Expr Op χ n → ExprStateM χ V S (Label Op V × ExprResult Op χ V n)
  | .ret vars => do
    let vals ← vars.mapM (.getVar _ _ _)
    return (.tau, .ret vals)
  | .op o args rets cont => do
    let argVals ← args.mapM (.getVar _ _ _)
    let retVals ← .liftS _ _ _ (OpInterp.interp o argVals)
    (rets.zip retVals).forM λ (v, val) => .setVar _ _ _ v val
    return (.op o argVals, .cont cont)
  | .br cond left right => do
    let condVal ← .getVar _ _ _ cond
    if OpInterp.asBool Op S condVal then
      return (.tau, .cont left)
    else
      return (.tau, .cont right)

abbrev ProcStateM := StateT S List
abbrev ChanUpdate := List (χ × V)

def ProcStateM.liftS (s : StateT S Option T) : ProcStateM S T := do
  match s.run (← get) with
  | none => .failure
  | some (val, state) =>
    set state
    return val

def ProcStateM.popInputs [DecidableEq χ]
  (inputs : Vector (InputBuf χ V) n) :
  ProcStateM S (Vector V n × Vector (InputBuf χ V) n) := do
  let vs ← inputs.mapM λ (var, buf) =>
    match buf with
    | [] => .failure
    | val :: rest => return (val, (var, rest))
  return (vs.map Prod.fst, vs.map Prod.snd)

/-- Fire the `i`-th atomic process and return the modified process with channel pushes. -/
def AtomicProc.step [DecidableEq χ] :
  AtomicProc Op χ V → ProcStateM S (Label Op V × AtomicProc Op χ V × ChanUpdate χ V)
  | .op o inputs outputs => do
    let (inputVals, inputs') ← .popInputs _ _ _ inputs
    let outputVals ← ProcStateM.liftS _ (OpInterp.interp o inputVals)
    return (
      .op o inputVals, .op o inputs' outputs,
      (outputs.zip outputVals).toList,
    )
  | .steer
      (decider, deciderVal :: restDecider)
      (input, inputVal :: restInput)
      output =>
    return (
      .tau, .steer (decider, restDecider) (input, restInput) output,
      if OpInterp.asBool Op S deciderVal then [(output, inputVal)]
      else [],
    )
  | .merge
      (decider, deciderVal :: restDecider)
      (input₁, inputVal₁ :: restInput₁)
      (input₂, inputVal₂ :: restInput₂)
      output =>
    return (
      .tau, .merge (decider, restDecider) (input₁, restInput₁) (input₂, restInput₂) output,
      if OpInterp.asBool Op S deciderVal then [(output, inputVal₁)]
      else [(output, inputVal₂)],
    )
  | .forward inputs outputs => do
    let (inputVals, inputs') ← .popInputs _ _ _ inputs
    return (.tau, .forward inputs' outputs, (outputs.zip inputVals).toList)
  | _ => .failure

def InputBuf.push [DecidableEq χ] (var : χ) (val : V) : InputBuf χ V → InputBuf χ V
  | (v, buf) => if v = var then (v, buf ++ [val]) else (v, buf)

def AtomicProc.push [DecidableEq χ] (var : χ) (val : V) : AtomicProc Op χ V → AtomicProc Op χ V
  | .op o inputs outputs =>
    .op o (inputs.map (InputBuf.push _ _ var val)) outputs
  | .steer decider input output =>
    .steer (InputBuf.push _ _ var val decider) (InputBuf.push _ _ var val input) output
  | .merge decider input₁ input₂ output =>
    .merge
      (InputBuf.push _ _ var val decider)
      (InputBuf.push _ _ var val input₁)
      (InputBuf.push _ _ var val input₂)
      output
  | .forward inputs outputs =>
    .forward (inputs.map (InputBuf.push _ _ var val)) outputs

def Proc.push [DecidableEq χ] (var : χ) (val : V) (p : Proc Op χ V) : Proc Op χ V :=
  p.map (AtomicProc.push _ _ _ var val)

def Proc.pushAll [DecidableEq χ] (updates : ChanUpdate χ V) (p : Proc Op χ V) : Proc Op χ V :=
  updates.foldl (λ p (var, val) => p.push _ _ _ var val) p

def Proc.step [DecidableEq χ] (p : Proc Op χ V) : ProcStateM S (Label Op V × Proc Op χ V) := do
  let m ← (List.finRange p.length).map (λ i => do
    let (lbl, ap, upd) ← p[i].step Op χ V S
    return (lbl, p.set i ap, upd))
  let (lbl, p', upd) ← m
  let p'' := Proc.pushAll _ _ _ upd p'
  return (lbl, p'')

end Semantics

section Examples

inductive MiniOp where
  | add
  | less
  | const (n : Nat)
  deriving Repr

instance : ToString MiniOp where
  toString | .add => "add"
           | .less => "less"
           | .const n => s!"const[{n}]"

instance : OpArity MiniOp where
  ι | .add => 2
    | .less => 2
    | .const _ => 0
  ω | .add => 1
    | .less => 1
    | .const _ => 1

def exampleExpr : Expr MiniOp String 1 :=
  .op .less #v["x", "y"] #v["b"] <|
  .br "b"
    (.op .add #v["x", "y"] #v["z"]
      (.ret #v["z"]))
    (.op (.const 42) #v[] #v["z"]
      (.ret #v["z"]))

#eval @compileTop MiniOp String _ 1 ℕ _ exampleExpr

end Examples
