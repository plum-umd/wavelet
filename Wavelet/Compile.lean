import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow

/-! A compiler from Seq to dataflow. -/

namespace Wavelet.Compile

open Op Seq Dataflow

universe u
variable (Op : Type u) (χ : Type u) (V S)
variable [Arity Op] [DecidableEq χ] [instInterp : Interp Op V S]

/--
Compiles an expression to a list of atomic processes, with
exactly `m + n + 1` outputs, where `m` is the number of parameters
of the encompassing function, `n` is the number of return values,
and the extra output is a Boolean indicating whether the expression
chooses to perform a tail call (with `m` arguments) or return
`n` final values.
-/
def compileExpr
  (wf : m > 0 ∧ n > 0) -- Additional well-formedness condition
  (definedVars : List χ)
  (pathConds : List (Bool × ChanName χ))
  : Expr Op χ m n → AtomicProcs Op (ChanName χ) V
  | .ret vars =>
    let chans := .empty _ (liveVars vars)
    let act := chans[0] -- Use the first return value as an activation signal
    [
      .forward chans retChans,
      -- No tail recursion, so we send junk values for the tail arguments
      -- and send `false` on the tail condition channel.
      .const (Interp.junkVal Op S) act tailArgs,
      .const (Interp.falseVal Op S) act #v[.tail_cond pathConds]
    ]
  | .tail vars =>
    let chans := .empty _ (liveVars vars)
    let act := chans[0]
    [
      .const (Interp.junkVal Op S) act retChans,
      .forward chans tailArgs,
      .const (Interp.trueVal Op S) act #v[.tail_cond pathConds]
    ]
  | .op o args rets cont =>
    let inputChans := .empty _ (liveVars args)
    let (definedVars', outputChans) := newVars rets
    (.op o inputChans outputChans) :: compileExpr wf definedVars' pathConds cont
  | .br cond left right =>
    let condChan := .empty _ (liveVar cond)
    let leftConds := (true, condChan.1) :: pathConds
    let rightConds := (false, condChan.1) :: pathConds
    let leftComp := compileExpr wf definedVars leftConds left
    let rightComp := compileExpr wf definedVars rightConds right
    [
      -- Steer all live variables
      .steer true condChan
        (.empty _ (allDefinedVars pathConds))
        (allDefinedVars leftConds),
      .steer false condChan
        (.empty _ (allDefinedVars pathConds))
        (allDefinedVars rightConds),
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
    liveVar v := .var v (definedVars.count v) pathConds
    liveVars {n} (vars : Vector χ n) := vars.map liveVar
    retChans := (Vector.range n).map λ i => .dest i pathConds
    tailArgs := (Vector.range m).map λ i => .tail_arg i pathConds
    newVars {k} (vs : Vector χ k) : List χ × Vector (ChanName χ) k :=
      (
        definedVars ++ vs.toList,
        vs.map λ v => .var v (definedVars.count v + 1) pathConds
      )
    allDefinedVars pathConds
      : Vector (ChanName χ) definedVars.eraseDups.length :=
      definedVars.eraseDups.toArray.toVector.map λ v =>
        .var v (definedVars.count v) pathConds
    exprOutputs m n pathConds := #v[ChanName.tail_cond pathConds] ++
      ((Vector.range n).map λ i => ChanName.dest i pathConds) ++
      ((Vector.range m).map λ i => ChanName.tail_arg i pathConds)
    brMerge m n condName condBuf pathConds :=
      let leftConds := (true, condName) :: pathConds
      let rightConds := (false, condName) :: pathConds
      .merge (.merge_cond condName, condBuf)
        (.empty _ (exprOutputs m n leftConds))
        (.empty _ (exprOutputs m n rightConds))
        (exprOutputs m n pathConds)

/-- Same as `compileExpr` but produces a `Proc` with well-defined inputs/outputs. -/
def compileExprAsProc
  (wf : m > 0 ∧ n > 0) -- Additional well-formedness condition
  (definedVars : List χ)
  (pathConds : List (Bool × ChanName χ))
  (expr : Expr Op χ m n)
  : Proc Op (ChanName χ) V definedVars.eraseDups.length (1 + n + m) :=
  {
    inputs := compileExpr.allDefinedVars _ definedVars pathConds,
    outputs := (.empty _ (compileExpr.exprOutputs _ m n pathConds)),
    atoms := compileExpr Op χ V S wf definedVars pathConds expr,
  }

/--
Compiles a function to a process with `m` inputs and `n` outputs.

Most of the compiled process should be a DAG, except for the back
edges of channels with the name `.tail_cond []` or `.tail_arg i []`.
-/
def compileFn
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
    bodyComp := compileExpr Op χ V S fn.NonEmptyIO fn.params.toList [] fn.body
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

end Wavelet.Compile
