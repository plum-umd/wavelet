import Mathlib.Logic.Relation
import Wavelet.Op

/-! Syntax and semantics for a simple imperative language. -/

namespace Wavelet.Seq

open Op

universe u
variable (Op : Type u) (χ : Type u)
variable [Arity Op]
variable [DecidableEq χ]

inductive Expr : Nat → Nat → Type u where
  | ret (vars : Vector χ n) : Expr m n
  | tail (vars : Vector χ m) : Expr m n
  | op (op : Op)
    (args : Vector χ (Arity.ι op))
    (bind : Vector χ (Arity.ω op))
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
structure Fn (m n : Nat) : Type u where
  params : Vector χ m
  body : Expr Op χ m n
  wf : m > 0 ∧ n > 0 ∧
    params.toList.Nodup ∧
    body.WellFormed _ _

def Fn.NonEmptyIO (fn : Fn Op χ m n) : m > 0 ∧ n > 0 :=
  ⟨fn.wf.1, fn.wf.2.1⟩

def Fn.WellFormedBody (fn : Fn Op χ m n) : fn.body.WellFormed _ _ :=
  fn.wf.2.2.2

/-- Consistently encoding Seq variables (`χ`) into channel names, used in
the compiler and also semantics of Seq to keep useful ghost states. -/
inductive ChanName where
  | var (base : χ) (count : Nat) (pathConds : List (Bool × ChanName))
  -- Only sent during branching
  | merge_cond (chan : ChanName)
  -- Only sent during ret/tail
  | dest (i : Nat) (pathConds : List (Bool × ChanName))
  -- Only sent during ret/tail
  | tail_arg (i : Nat) (pathConds : List (Bool × ChanName))
  -- Only sent during ret/tail
  | tail_cond (pathConds : List (Bool × ChanName))
  -- Only sent during the final steers
  | final_dest (i : Nat)
  | final_tail_arg (i : Nat)
  deriving Repr

/- From this point onwards, assume a fixed operator semantics. -/
variable (V S) [instInterp : Interp Op V S]

/-- TODO: should be auto-derived -/
instance : DecidableEq (ChanName χ) := sorry

/-- Partial map from variables. -/
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
structure ExprState (m n : Nat) where
  fn : Fn Op χ m n
  vars : VarMap χ V
  state : S
  -- Ghost states for the simulation relation
  definedVars : List χ
  pathConds : List (Bool × ChanName χ)

inductive ExprResult (m n : Nat) where
  | ret (vals : Vector V n)
  | cont (expr : Expr Op χ m n)

structure Config m n where
  expr : ExprResult Op χ V m n
  estate : ExprState Op χ V S m n

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

/-- Initialize an expression configuration. -/
def Config.init
  (fn : Fn Op χ m n)
  (state : S)
  (args : Vector V m) : Config Op χ V S m n
  := {
    expr := .cont fn.body,
    estate := ExprState.init _ _ _ _ fn state args,
  }

/-- Small-step operational semantics for Seq. -/
inductive Config.Step : Config Op χ V S m n → Config Op χ V S m n → Prop where
  | step_ret :
    c.expr = .cont (.ret args) →
    c.estate.vars.getVars _ _ args = some inputVals →
    Step c {
      expr := .ret inputVals,
      estate := c.estate,
    }
  | step_tail :
    c.expr = .cont (.tail args) →
    c.estate.vars.getVars _ _ args = some inputVals →
    Step c {
      expr := .cont c.estate.fn.body,
      estate := .init _ _ _ _ c.estate.fn c.estate.state inputVals,
    }
  | step_op
    {o inputVals outputVals state'}
    {args : Vector χ (Arity.ι o)}
    {rets cont} :
    c.expr = .cont (.op o args rets cont) →
    c.estate.vars.getVars _ _ args = some inputVals →
    (instInterp.interp o inputVals).run c.estate.state = some (outputVals, state') →
    Step c {
      expr := .cont cont,
      estate := { c.estate with
        vars := c.estate.vars.insertVars _ _ rets outputVals,
        definedVars := c.estate.definedVars ++ rets.toList,
        state := state',
      },
    }
  | step_br {cond} :
    c.expr = .cont (.br cond left right) →
    c.estate.vars.getVar _ _ cond = some condVal →
    Step c {
      expr := if instInterp.asBool condVal then .cont left else .cont right,
      estate := {
        c.estate with
        pathConds :=
          (
            instInterp.asBool condVal,
            .var cond (c.estate.definedVars.count cond) c.estate.pathConds,
          )
          :: c.estate.pathConds,
      },
    }

def Config.StepPlus {m n} := @Relation.TransGen (Config Op χ V S m n) (Step Op χ V S)
def Config.StepStar {m n} := @Relation.ReflTransGen (Config Op χ V S m n) (Step Op χ V S)

inductive EvalResult (m n : Nat) where
  | ret (vals : Vector V n)
  | tail (args : Vector V m)

/-- A simple big-step semantics of expressions -/
def Expr.eval (locals : VarMap χ V)
  : Expr Op χ m n → StateT S Option (EvalResult V m n)
  | .ret vars => do
    let vals ← locals.getVars _ _ vars
    return .ret vals
  | .tail vars => do
    let vals ← locals.getVars _ _ vars
    return .tail vals
  | .op o args rets cont => do
    let inputVals ← locals.getVars _ _ args
    let outputVals ← instInterp.interp o inputVals
    let locals := locals.insertVars _ _ rets outputVals
    eval locals cont
  | .br cond left right => do
    let condVal ← locals.getVar _ _ cond
    if instInterp.asBool condVal then
      eval locals left
    else
      eval locals right

end Wavelet.Seq
