import Mathlib.Data.List.Basic
import Mathlib.Data.PNat.Basic

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

def ChanBuf.push (buf : ChanBuf χ V) (val : V) : ChanBuf χ V :=
  (buf.1, buf.2.concat val)

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

/-
 ██████╗ ██████╗ ███╗   ███╗██████╗ ██╗██╗     ███████╗██████╗
██╔════╝██╔═══██╗████╗ ████║██╔══██╗██║██║     ██╔════╝██╔══██╗
██║     ██║   ██║██╔████╔██║██████╔╝██║██║     █████╗  ██████╔╝
██║     ██║   ██║██║╚██╔╝██║██╔═══╝ ██║██║     ██╔══╝  ██╔══██╗
╚██████╗╚██████╔╝██║ ╚═╝ ██║██║     ██║███████╗███████╗██║  ██║
 ╚═════╝ ╚═════╝ ╚═╝     ╚═╝╚═╝     ╚═╝╚══════╝╚══════╝╚═╝  ╚═╝

We define compilers from `Expr` and `Fn` to `Proc`.
-/

variable [DecidableEq χ]

inductive ChanName where
  | var (base : χ) (count : ℕ) (pathConds : List (Bool × ChanName))
  | merge_cond (chan : ChanName)
  | dest (i : ℕ) (pathConds : List (Bool × ChanName))
  | tail_arg (i : ℕ) (pathConds : List (Bool × ChanName))
  | tail_cond (pathConds : List (Bool × ChanName))
  | final_dest (i : ℕ)
  | final_tail_arg (i : ℕ)
  deriving Repr

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

def Fn.compile
  (fn : Fn Op χ m n) : Option (Proc Op (ChanName χ) V m n)
  :=
  let bodyComp := fn.body.compile Op χ V S fn.wf fn.params.toList []
  return {
    inputs := fn.params.map λ v => .var v 0 [],
    outputs := (Vector.range n).map λ i => .empty _ (.dest i []),
    atoms := [
      -- A carry gate to merge initial values and tail call arguments
      .carry
        false
        (.empty _ (.tail_cond []))
        (fn.params.map λ v => .empty _ (.var v 0 []))
        ((Vector.range m).map λ i => .empty _ (.final_tail_arg i))
        (fn.params.map λ v => .var v 1 []),
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
    ] ++ bodyComp
  }
