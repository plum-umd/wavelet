import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Lemmas

/-! A compiler from Seq to dataflow. -/

namespace Wavelet.Compile

open Op Seq Dataflow

/--
TODO: These are originally specified in the `where`
clause of `compileExpr`, but I hit this issue:
https://github.com/leanprover/lean4/issues/10559
-/
def compileExpr.allVarsExcept
  [DecidableEq χ]
  (definedVars vs : List χ)
  (pathConds : List (Bool × ChanName χ)) :
  Vector (ChanName χ) (definedVars.removeAll vs).length :=
  (definedVars.removeAll vs).toVector.map (.var · pathConds)

/-- Output channels of a compiled expression,
essentially `return values ⊕ tail call arguments`. -/
def compileExpr.exprOutputs
  m n (pathConds : List (Bool × ChanName χ))
  : Vector (ChanName χ) (n + (m + 1))
  := (Vector.range n).map (ChanName.dest · pathConds) ++
    (((Vector.range m).map (ChanName.tail_arg · pathConds)).push
    (ChanName.tail_cond pathConds))

def compileExpr.tailExprOutputs
  m n (pathConds : List (Bool × ChanName χ))
  : Vector (ChanName χ) (m + (n + 1))
  := (Vector.range m).map (ChanName.tail_arg · pathConds) ++
    ((Vector.range n).map (ChanName.dest · pathConds)).push
    (ChanName.tail_cond pathConds)

/-- Merge operator generated for each branching expression. -/
def compileExpr.branchMerge
  [Arity Op]
  (m n : Nat)
  (condName : ChanName χ)
  (pathConds : List (Bool × ChanName χ))
  : AtomicProc Op (ChanName χ) V :=
  let leftConds := (true, condName) :: pathConds
  let rightConds := (false, condName) :: pathConds
  .merge (.merge_cond condName)
    (compileExpr.exprOutputs m n leftConds)
    (compileExpr.exprOutputs m n rightConds)
    (compileExpr.exprOutputs m n pathConds)

/--
Compiles an expression to a list of atomic processes, with
exactly `m + n + 1` outputs, where `m` is the number of parameters
of the encompassing function, `n` is the number of return values,
and the extra output is a Boolean indicating whether the expression
chooses to perform a tail call (with `m` arguments) or return
`n` final values.
-/
def compileExpr
  [Arity Op] [InterpConsts V] [DecidableEq χ]
  (hnz : m > 0 ∧ n > 0)
  (definedVars : List χ)
  (pathConds : List (Bool × ChanName χ))
  : Expr Op χ m n → AtomicProcs Op (ChanName χ) V
  | .ret vars =>
    let chans := vars.map (.var · pathConds)
    let junks : Vector V m := Vector.replicate m InterpConsts.junkVal
    let falseVal : V := InterpConsts.fromBool false
    let consts : Vector V (m + 1) := junks ++ #v[falseVal]
    [
      .forwardc
        chans consts
        (compileExpr.exprOutputs m n pathConds),
      -- Discard all other variables
      .sink (compileExpr.allVarsExcept definedVars vars.toList pathConds),
    ]
  | .tail vars =>
    let chans := vars.map (.var · pathConds)
    let junks : Vector V n := Vector.replicate n InterpConsts.junkVal
    let trueVal : V := InterpConsts.fromBool true
    let consts : Vector V (n + 1) := junks ++ #v[trueVal]
    [
      .forwardc
        chans consts
        (compileExpr.tailExprOutputs m n pathConds),
      -- Discard all other variables
      .sink (compileExpr.allVarsExcept definedVars vars.toList pathConds),
    ]
  | .op o args rets cont =>
    let inputChans := args.map (.var · pathConds)
    (.op o inputChans (rets.map (.var · pathConds))) ::
      compileExpr hnz
        (definedVars.removeAll args.toList ++ rets.toList)
        pathConds cont
  | .br cond left right =>
    let condChan := .var cond pathConds
    let leftConds := (true, condChan) :: pathConds
    let rightConds := (false, condChan) :: pathConds
    let leftComp := compileExpr hnz
      (definedVars.removeAll [cond]) leftConds left
    let rightComp := compileExpr hnz
      (definedVars.removeAll [cond]) rightConds right
    [
      -- Copy condition variables
      .fork condChan #v[.switch_cond condChan, .merge_cond condChan],
      -- Steer all live variables
      .switch (.switch_cond condChan)
        (compileExpr.allVarsExcept definedVars [cond] pathConds)
        (compileExpr.allVarsExcept definedVars [cond] leftConds)
        (compileExpr.allVarsExcept definedVars [cond] rightConds),
    ] ++ leftComp ++ rightComp ++ [
      -- Merge tail call conditions, return values and tail call arguments
      -- from both branches. This is done at the end so that we can keep
      -- the graph as "acyclic" as possible.
      compileExpr.branchMerge m n condChan pathConds
    ]

/--
Compiles a function to a process with `m` inputs and `n` outputs.

Most of the compiled process should be a DAG, except for the back
edges of channels with the name `.tail_cond []` or `.tail_arg i []`.
-/
def compileFn
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (hnz : m > 0 ∧ n > 0)
  (fn : Fn Op χ m n) : Proc Op (ChanName χ) V m n
  := {
    inputs,
    outputs := (Vector.range n).map .final_tail_arg,
    atoms := initCarry false :: (bodyComp ++ resultSteers m n)
  }
  where
    -- A carry gate to merge initial values and tail call arguments
    inputs := fn.params.map .input
    initCarry inLoop :=
      .carry inLoop
        .tail_cond_carry
        inputs
        ((Vector.range m).map .final_tail_arg)
        (fn.params.map λ v => .var v [])
    bodyComp := compileExpr hnz
      fn.params.toList [] fn.body
    resultSteers m n := [
      .fork (.tail_cond []) #v[
        .tail_cond_carry,
        .tail_cond_steer_dests,
        .tail_cond_steer_tail_args,
      ],
      -- If tail condition is true, discard the junk return values
      .steer false
        .tail_cond_steer_dests
        ((Vector.range n).map (.dest · []))
        ((Vector.range n).map .final_dest),
      -- If tail condition is false, discard the junk tail arguments
      .steer true
        .tail_cond_steer_tail_args
        ((Vector.range m).map (.tail_arg · []))
        ((Vector.range m).map .final_tail_arg),
    ]

end Wavelet.Compile
