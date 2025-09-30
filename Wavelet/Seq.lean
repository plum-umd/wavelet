import Mathlib.Logic.Relation
import Wavelet.Op
import Wavelet.LTS

/-! Syntax and semantics for a simple imperative language. -/

namespace Wavelet.Seq

open Op LTS

/-- `Expr ... m n` is an expression that can either return `n`
output values, or trigger a tail call with `m` values. -/
inductive Expr (Op : Type u) (χ : Type v) [instArity : Arity Op]
  : Nat → Nat → Type (max u v) where
  | ret (vars : Vector χ n) : Expr Op χ m n
  | tail (vars : Vector χ m) : Expr Op χ m n
  | op (op : Op)
    (args : Vector χ (Arity.ι op))
    (rets : Vector χ (Arity.ω op))
    (cont : Expr Op χ m n) : Expr Op χ m n
  | br
    (cond : χ)
    (left : Expr Op χ m n)
    (right : Expr Op χ m n) : Expr Op χ m n
  -- | call
  --   (args : Vector χ m')
  --   (params : Vector χ m')
  --   (body : Expr Op χ m' n')
  --   (rets : Vector χ n')
  --   (cont : Expr Op χ m n) : Expr Op χ m n

/--
Some static constraints on expressions:
1. Bound variables are disjoint
2. Use of variables is affine
3. No shadowing
-/
inductive Expr.WellFormed [Arity Op] [DecidableEq χ]
  : List χ → Expr Op χ n m → Prop where
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
    WellFormed (definedVars.removeAll [c]) left →
    WellFormed (definedVars.removeAll [c]) right →
    WellFormed definedVars (.br c left right)
  -- | wf_iter :
  --   args.toList.Nodup →
  --   params.toList.Nodup →
  --   WellFormed params.toList body →
  --   WellFormed (definedVars.removeAll args.toList ++ rets.toList) cont →
  --   WellFormed definedVars (.iter args params body rets cont)

/-- `Fn m n` is a function with `m` inputs and `n` outputs. -/
structure Fn (Op χ) [instArity : Arity Op] m n where
  params : Vector χ m
  body : Expr Op χ m n

def Fn.WellFormed [Arity Op] [DecidableEq χ]
  (fn : Fn Op χ m n) : Prop :=
  fn.params.toList.Nodup ∧
  fn.body.WellFormed fn.params.toList


/-- Consistently encoding Seq variables (`χ`) into channel names, used in
the compiler and also semantics of Seq to keep useful ghost states. -/
inductive ChanName (χ : Type u) where
  -- Inputs to a function's carry gates
  | input (base : χ)
  | var (base : χ) (pathConds : List (Bool × ChanName χ))
  -- Only sent during branching
  | switch_cond (chan : ChanName χ)
  | merge_cond (chan : ChanName χ)
  -- Only sent during ret/tail
  | dest (i : Nat) (pathConds : List (Bool × ChanName χ))
  -- Only sent during ret/tail
  | tail_arg (i : Nat) (pathConds : List (Bool × ChanName χ))
  -- Only sent during ret/tail
  | tail_cond (pathConds : List (Bool × ChanName χ))
  | tail_cond_carry
  | tail_cond_steer_dests
  | tail_cond_steer_tail_args
  -- Only sent during the final steers
  | final_dest (i : Nat)
  | final_tail_arg (i : Nat)
  deriving Repr

/-- TODO: should be auto-derived -/
instance [inst : DecidableEq χ] : DecidableEq (ChanName χ) := sorry

/-- Partial map from variables. -/
abbrev VarMap χ V := χ → Option V

def VarMap.empty : VarMap χ V := λ _ => none

def VarMap.insertVars
  [DecidableEq χ]
  (vars : Vector χ n)
  (vals : Vector V n)
  (m : VarMap χ V) : VarMap χ V :=
  λ v => ((vars.zip vals).toList.find? (·.1 = v)).map (·.2) <|> m v

def VarMap.getVar (v : χ) (m : VarMap χ V) : Option V := m v

def VarMap.getVars
  (vars : Vector χ n)
  (m : VarMap χ V) : Option (Vector V n) :=
  vars.mapM m

def VarMap.fromList [DecidableEq χ] (kvs : List (χ × V)) : VarMap χ V :=
  λ v => (kvs.find? (·.1 = v)).map (·.2)

def VarMap.removeVar [DecidableEq χ] (v : χ) (m : VarMap χ V) : VarMap χ V :=
  λ v' => if v = v' then none else m v'

def VarMap.removeVars [DecidableEq χ] (vars : List χ) (m : VarMap χ V) : VarMap χ V :=
  λ v => if v ∈ vars then none else m v

inductive ExprResult Op χ V [Arity Op] (m n : Nat) where
  | ret (vals : Vector V n)
  | cont (expr : Expr Op χ m n)

/-- State of expression execution. -/
structure Config (Op : Type u₁) (χ : Type u₂) (V : Type u₃) (S : Type u₄) [Arity Op] m n where
  expr : ExprResult Op χ V m n
  fn : Fn Op χ m n
  vars : VarMap χ V
  state : S
  -- Ghost state for the simulation relation
  definedVars : List χ
  pathConds : List (Bool × ChanName χ)

/-- Initialize an expression configuration. -/
def Config.init
  [Arity Op] [DecidableEq χ]
  (fn : Fn Op χ m n)
  (state : S)
  (args : Vector V m) : Config Op χ V S m n
  := {
    expr := .cont fn.body,
    fn,
    vars := .fromList (fn.params.zip args).toList,
    state,
    definedVars := fn.params.toList,
    pathConds := [],
  }

/-- Small-step operational semantics for Seq. -/
inductive Config.Step
  {Op χ V E S m n}
  [Arity Op] [InterpConsts V] [interp : InterpOp Op V E S] [DecidableEq χ]
  : LTS (Config Op χ V S m n) E where
  | step_ret :
    c.expr = .cont (.ret args) →
    c.vars.getVars args = some inputVals →
    Step c .ε { c with
      expr := .ret inputVals,
      vars := VarMap.empty,
      definedVars := [],
      pathConds := [],
    }
  | step_tail :
    c.expr = .cont (.tail args) →
    c.vars.getVars args = some inputVals →
    Step c .ε (.init c.fn c.state inputVals)
  | step_op_trans
    {o inputVals state'}
    {args : Vector χ (Arity.ι o)}
    {rets cont} :
    c.expr = .cont (.op o args rets cont) →
    c.vars.getVars args = some inputVals →
    InterpOp.Step o inputVals c.state tr (state', none) →
    Step c tr { c with state := state' }
  | step_op_final
    {o inputVals outputVals state'}
    {args : Vector χ (Arity.ι o)}
    {rets cont} :
    c.expr = .cont (.op o args rets cont) →
    c.vars.getVars args = some inputVals →
    InterpOp.Step o inputVals c.state tr (state', some outputVals) →
    Step c tr { c with
      expr := .cont cont,
      vars := (c.vars.removeVars args.toList).insertVars rets outputVals,
      state := state',
      definedVars := (c.definedVars.removeAll args.toList) ++ rets.toList,
    }
  | step_br {cond : χ} :
    c.expr = .cont (.br cond left right) →
    c.vars.getVar cond = some condVal →
    InterpConsts.toBool condVal = some condBool →
    Step c .ε { c with
      expr := .cont (if condBool then left else right),
      vars := c.vars.removeVar cond,
      definedVars := c.definedVars.removeAll [cond],
      pathConds :=
        (condBool, .var cond c.pathConds) :: c.pathConds,
    }

abbrev Config.StepPlus
  [Arity Op] [InterpConsts V] [InterpOp Op V E S] [DecidableEq χ]
  : LTS (Config Op χ V S m n) E := Step.Plus

abbrev Config.StepStar
  [Arity Op] [InterpConsts V] [InterpOp Op V E S] [DecidableEq χ]
  : LTS (Config Op χ V S m n) E := Step.Star

end Wavelet.Seq
