import Mathlib.Logic.Relation
import Wavelet.Semantics.Defs

import Wavelet.Seq.VarMap

/-! Syntax and semantics for a simple imperative language. -/

namespace Wavelet.Seq

open Semantics

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

/-- `Fn m n` is a function with `m` inputs and `n` outputs. -/
structure Fn Op χ (V : Type u) [instArity : Arity Op] m n where
  params : Vector χ m
  body : Expr Op χ m n

def Fn.WellFormed [Arity Op] [DecidableEq χ]
  (fn : Fn Op χ V m n) : Prop :=
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

inductive Cont Op χ [Arity Op] m n where
  | init
  | expr (e : Expr Op χ m n)

/-- State of expression execution. -/
structure Config (Op : Type u₁) (χ : Type u₂) (V : Type u₃) [Arity Op] m n where
  cont : Cont Op χ m n
  fn : Fn Op χ V m n
  vars : VarMap χ V
  -- Ghost state for the simulation relation
  definedVars : List χ
  pathConds : List (Bool × ChanName χ)

/-- Initialize an expression configuration. -/
def Config.init
  [Arity Op] [DecidableEq χ]
  (fn : Fn Op χ V m n) : Config Op χ V m n
  := {
    cont := .init,
    fn,
    vars := .empty,
    definedVars := [],
    pathConds := [],
  }

/-- Small-step operational semantics for Seq. -/
inductive Config.Step
  [Arity Op] [InterpConsts V] [DecidableEq χ]
  : Lts (Config Op χ V m n) (Label Op V m n) where
  | step_init :
    c.cont = .init →
    Step c (.input args) { c with
      cont := .expr c.fn.body,
      vars := .fromList (c.fn.params.zip args).toList,
      definedVars := c.fn.params.toList,
      pathConds := [],
    }
  | step_ret :
    c.cont = .expr (.ret args) →
    c.vars.getVars args = some retVals →
    Step c (.output retVals) { c with
      cont := .init,
      vars := .empty,
      definedVars := [],
      pathConds := [],
    }
  | step_tail :
    c.cont = .expr (.tail args) →
    c.vars.getVars args = some tailArgs →
    Step c .τ { c with
      cont := .expr c.fn.body,
      vars := .fromList (c.fn.params.zip tailArgs).toList,
      definedVars := c.fn.params.toList,
      pathConds := [],
    }
  | step_op
    {args : Vector χ (Arity.ι op)}
    {rets cont} :
    c.cont = .expr (.op op args rets cont) →
    c.vars.getVars args = some inputVals →
    Step c (.yield op inputVals outputVals) { c with
      cont := .expr cont,
      vars := (c.vars.removeVars args.toList).insertVars rets outputVals,
      definedVars := (c.definedVars.removeAll args.toList) ++ rets.toList,
    }
  | step_br {cond : χ} :
    c.cont = .expr (.br cond left right) →
    c.vars.getVar cond = some condVal →
    InterpConsts.toBool condVal = some condBool →
    Step c .τ { c with
      cont := .expr (if condBool then left else right),
      vars := c.vars.removeVar cond,
      definedVars := c.definedVars.removeAll [cond],
      pathConds :=
        (condBool, .var cond c.pathConds) :: c.pathConds,
    }

/-- `Semantics` implementation of a function. -/
def Fn.semantics
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (fn : Fn Op χ V m n) : Semantics Op V m n := {
    S := Config Op χ V m n,
    init := Config.init fn,
    lts := Config.Step,
  }

end Wavelet.Seq
