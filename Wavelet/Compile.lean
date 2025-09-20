import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Lemmas

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
  (hnz : m > 0 ∧ n > 0)
  (definedVars : List χ)
  (pathConds : List (Bool × ChanName χ))
  : Expr Op χ m n → AtomicProcs Op (ChanName χ) V
  | .ret vars =>
    let chans := varNames vars
    let act := chans[0] -- Use the first return value as an activation signal
    [
      .forward chans retChans,
      -- No tail recursion, so we send junk values for the tail arguments
      -- and send `false` on the tail condition channel.
      .const (Interp.junkVal Op S) act tailArgs,
      .const (Interp.falseVal Op S) act #v[.tail_cond pathConds]
    ]
  | .tail vars =>
    let chans := varNames vars
    let act := chans[0]
    [
      .const (Interp.junkVal Op S) act retChans,
      .forward chans tailArgs,
      .const (Interp.trueVal Op S) act #v[.tail_cond pathConds]
    ]
  | .op o args rets cont =>
    let inputChans := varNames args
    (.op o inputChans (varNames rets)) ::
      compileExpr hnz (definedVars.removeAll args.toList ++ rets.toList) pathConds cont
  | .br cond left right =>
    let condChan := varName cond
    let leftConds := (true, condChan) :: pathConds
    let rightConds := (false, condChan) :: pathConds
    let leftComp := compileExpr hnz (definedVars.erase cond) leftConds left
    let rightComp := compileExpr hnz (definedVars.erase cond) rightConds right
    [
      -- Copy condition variables
      .fork condChan #v[.switch_cond condChan, .merge_cond condChan],
      -- Steer all live variables
      .switch (.switch_cond condChan)
        (allVarsExcept cond pathConds)
        (allVarsExcept cond leftConds)
        (allVarsExcept cond rightConds),
    ] ++ leftComp ++ rightComp ++ [
      -- Merge tail call conditions, return values and tail call arguments
      -- from both branches. This is done at the end so that we can keep
      -- the graph as "acyclic" as possible.
      brMerge m n condChan pathConds
    ]
  where
    -- Current variable names
    varName v := .var v pathConds
    varNames {n} (vars : Vector χ n) := vars.map varName
    retChans := (Vector.range n).map (.dest · pathConds)
    tailArgs := (Vector.range m).map (.tail_arg · pathConds)
    allVarsExcept v pathConds := (definedVars.erase v).toVector.map (.var · pathConds)
    exprOutputs m n pathConds := #v[ChanName.tail_cond pathConds] ++
      ((Vector.range n).map (ChanName.dest · pathConds)) ++
      ((Vector.range m).map (ChanName.tail_arg · pathConds))
    brMerge m n condName pathConds :=
      let leftConds := (true, condName) :: pathConds
      let rightConds := (false, condName) :: pathConds
      .merge (.merge_cond condName)
        (exprOutputs m n leftConds)
        (exprOutputs m n rightConds)
        (exprOutputs m n pathConds)

/--
Compiles a function to a process with `m` inputs and `n` outputs.

Most of the compiled process should be a DAG, except for the back
edges of channels with the name `.tail_cond []` or `.tail_arg i []`.
-/
def compileFn
  (hnz : m > 0 ∧ n > 0)
  (fn : Fn Op χ m n) : Proc Op (ChanName χ) V m n
  :=
  {
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
    bodyComp := compileExpr Op χ V S hnz fn.params.toList [] fn.body
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
