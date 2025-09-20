import Mathlib.Logic.Relation
import Wavelet.Op

/-! Syntax and semantics for a simple imperative language. -/

namespace Wavelet.Seq

open Op

universe u
variable (Op : Type u) (χ : Type u)
variable [instArity : Arity Op]
variable [DecidableEq χ]

inductive Expr : Nat → Nat → Type u where
  | ret (vars : Vector χ n) : Expr m n
  | tail (vars : Vector χ m) : Expr m n
  | op (op : Op)
    (args : Vector χ (Arity.ι op))
    (bind : Vector χ (Arity.ω op))
    (cont : Expr m n) : Expr m n
  | br (cond : χ) (left : Expr m n) (right : Expr m n) : Expr m n

/--
Some static, non-typing constraints on expressions:
1. Bounded variables are disjoint
2. Use of variables is affine
3. No shadowing
-/
inductive Expr.WellFormed : List χ → Expr Op χ n m → Prop where
  | wf_ret :
    vars.toList.Nodup →
    WellFormed definedVars (.ret vars)
  | wf_tail :
    vars.toList.Nodup →
    WellFormed definedVars (.tail vars)
  | wf_op :
    args.toList.Nodup →
    rets.toList.Nodup →
    definedVars.Disjoint rets.toList →
    args.toList ⊆ definedVars →
    WellFormed ((definedVars.removeAll args.toList) ++ rets.toList) cont →
    WellFormed definedVars (.op o args rets cont)
  | wf_br :
    WellFormed (definedVars.erase c) left →
    WellFormed (definedVars.erase c) right →
    WellFormed definedVars (.br c left right)

/-- `Fn m n` is a function with `m` inputs and `n` outputs. -/
structure Fn (m n : Nat) : Type u where
  params : Vector χ m
  body : Expr Op χ m n

def Fn.WellFormed (fn : Fn Op χ m n) : Prop :=
  fn.params.toList.Nodup ∧
  fn.body.WellFormed _ _ fn.params.toList

/-- Consistently encoding Seq variables (`χ`) into channel names, used in
the compiler and also semantics of Seq to keep useful ghost states. -/
inductive ChanName where
  -- Inputs to a function's carry gates
  | input (base : χ)
  | var (base : χ) (pathConds : List (Bool × ChanName))
  -- Only sent during branching
  | switch_cond (chan : ChanName)
  | merge_cond (chan : ChanName)
  -- Only sent during ret/tail
  | dest (i : Nat) (pathConds : List (Bool × ChanName))
  -- Only sent during ret/tail
  | tail_arg (i : Nat) (pathConds : List (Bool × ChanName))
  -- Only sent during ret/tail
  | tail_cond (pathConds : List (Bool × ChanName))
  | tail_cond_carry
  | tail_cond_steer_dests
  | tail_cond_steer_tail_args
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

def VarMap.fromList (kvs : List (χ × V)) : VarMap χ V :=
  λ v => (kvs.find? (·.1 = v)).map (·.2)

def VarMap.removeVar (v : χ) (m : VarMap χ V) : VarMap χ V :=
  λ v' => if v = v' then none else m v'

def VarMap.removeVars (vars : List χ) (m : VarMap χ V) : VarMap χ V :=
  λ v => if v ∈ vars then none else m v

inductive ExprResult (m n : Nat) where
  | ret (vals : Vector V n)
  | cont (expr : Expr Op χ m n)

/-- State of expression execution. -/
structure Config m n where
  expr : ExprResult Op χ V m n
  fn : Fn Op χ m n
  vars : VarMap χ V
  state : S
  -- Ghost state for the simulation relation
  definedVars : List χ
  pathConds : List (Bool × ChanName χ)

/-- Initialize an expression configuration. -/
def Config.init
  (fn : Fn Op χ m n)
  (state : S)
  (args : Vector V m) : Config Op χ V S m n
  := {
    expr := .cont fn.body,
    fn,
    vars := .fromList _ _ (fn.params.zip args).toList,
    state,
    definedVars := fn.params.toList,
    pathConds := [],
  }

/-- Small-step operational semantics for Seq. -/
inductive Config.Step : Config Op χ V S m n → Config Op χ V S m n → Prop where
  | step_ret :
    c.expr = .cont (.ret args) →
    c.vars.getVars _ _ args = some inputVals →
    Step c { c with
      expr := .ret inputVals,
      vars := c.vars.removeVars _ _ args.toList,
      definedVars := c.definedVars.removeAll args.toList,
    }
  | step_tail :
    c.expr = .cont (.tail args) →
    c.vars.getVars _ _ args = some inputVals →
    Step c (.init _ _ _ _ c.fn c.state inputVals)
  | step_op
    {o inputVals outputVals state'}
    {args : Vector χ (Arity.ι o)}
    {rets cont} :
    c.expr = .cont (.op o args rets cont) →
    c.vars.getVars _ _ args = some inputVals →
    (instInterp.interp o inputVals).run c.state = some (outputVals, state') →
    Step c { c with
      expr := .cont cont,
      vars := (c.vars.removeVars _ _ args.toList).insertVars _ _ rets outputVals,
      state := state',
      definedVars := (c.definedVars.removeAll args.toList) ++ rets.toList,
    }
  | step_br {cond} :
    c.expr = .cont (.br cond left right) →
    c.vars.getVar _ _ cond = some condVal →
    Step c { c with
      expr := if instInterp.asBool condVal then .cont left else .cont right,
      vars := c.vars.removeVar _ _ cond,
      definedVars := c.definedVars.erase cond,
      pathConds :=
        (
          instInterp.asBool condVal,
          .var cond c.pathConds,
        ) :: c.pathConds,
    }

def Config.StepPlus {m n} := @Relation.TransGen (Config Op χ V S m n) (Step Op χ V S)
def Config.StepStar {m n} := @Relation.ReflTransGen (Config Op χ V S m n) (Step Op χ V S)

end Wavelet.Seq
