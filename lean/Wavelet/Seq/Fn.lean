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

/-- `Fn m n` is a function with `m` inputs and `n` outputs. -/
structure Fn Op χ (V : Type u) [instArity : Arity Op] m n where
  params : Vector χ m
  body : Expr Op χ m n

inductive Cont Op χ [Arity Op] m n where
  | init
  | expr (e : Expr Op χ m n)

/-- State of expression execution. -/
structure Config (Op : Type u₁) (χ : Type u₂) (V : Type u₃) [Arity Op] m n : Type (max u₁ u₂ u₃) where
  cont : Cont Op χ m n
  fn : Fn Op χ V m n
  vars : VarMap χ V

/-- Initialize an expression configuration. -/
def Config.init
  [Arity Op] [DecidableEq χ]
  (fn : Fn Op χ V m n) : Config Op χ V m n
  := {
    cont := .init,
    fn,
    vars := .empty,
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
    }
  | step_ret :
    c.cont = .expr (.ret args) →
    c.vars.getVars args = some retVals →
    Step c (.output retVals) { c with
      cont := .init,
      vars := .empty,
    }
  | step_tail :
    c.cont = .expr (.tail args) →
    c.vars.getVars args = some tailArgs →
    Step c .τ { c with
      cont := .expr c.fn.body,
      vars := .fromList (c.fn.params.zip tailArgs).toList,
    }
  | step_op
    {args : Vector χ (Arity.ι op)}
    {rets cont} :
    c.cont = .expr (.op op args rets cont) →
    c.vars.getVars args = some inputVals →
    Step c (.yield op inputVals outputVals) { c with
      cont := .expr cont,
      vars := (c.vars.removeVars args.toList).insertVars rets outputVals,
    }
  | step_br {cond : χ} :
    c.cont = .expr (.br cond left right) →
    c.vars.getVar cond = some condVal →
    InterpConsts.toBool condVal = some condBool →
    Step c .τ { c with
      cont := .expr (if condBool then left else right),
      vars := c.vars.removeVar cond,
    }

/-- `Semantics` implementation of a function. -/
def Fn.semantics
  {Op : Type u} {χ : Type v} {V : Type w}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (fn : Fn Op χ V m n) : Semantics.{_, _, max u v w} Op V m n := {
    S := Config Op χ V m n,
    init := Config.init fn,
    lts := Config.Step,
  }

end Wavelet.Seq
