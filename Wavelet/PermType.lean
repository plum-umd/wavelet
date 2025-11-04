import Wavelet.Determinacy
import Wavelet.Seq.AffineVar

/-!
Permission type system and its soundness for `Seq`.

Note that as of now, the typing relation is described
more like a meta-theory statement about the "symbolic"
execution of `Prog`/`Fn`/`Expr`, without concrete and
executable representation of dependent premissions.

There is an executable but unverified version of this
type system in Rust (TODO: link).
-/

namespace Wavelet.Seq

open Semantics Determinacy

/-- Typing context -/
structure Ctx χ V T where
  vars : VarMap χ V
  perms : VarMap χ T

inductive ProgWithSpec.WellPermTypedExpr
  [Arity Op] [PCM T] [DecidableEq χ]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  (progSpec : ProgSpec V T sigs)
  (i : Fin k) :
    Ctx χ V T →
    Expr (WithSpec Op opSpec ⊕ SigOps (extendSigs sigs) i.castSucc)
      χ (extendSigs sigs i).ι (extendSigs sigs i).ω →
    Prop where
  | wpt_ret :
    ctx.vars.getVars vars.pop = some retVals →
    ctx.perms.getVar vars.back = some retPerm →
    retPerm = (progSpec i).post retVals →
    WellPermTypedExpr progSpec i ctx (.ret vars)
  | wpt_tail :
    ctx.vars.getVars vars.pop = some vals →
    ctx.perms.getVar vars.back = some tailPerm →
    tailPerm = (progSpec i).pre vals →
    WellPermTypedExpr progSpec i ctx (.tail vars)
  -- Calls to an ordinary operator with a permission token.
  | wpt_op_ghost
    {args : Vector χ (Arity.ι op + 1)}
    {rets : Vector χ (Arity.ω op + 1)}
    {inputVals : Vector V (Arity.ι op)} :
    ctx.vars.getVars args.pop = some inputVals →
    ctx.perms.getVar args.back = some perm →
    perm = opSpec.pre op inputVals →
    -- Overapproximating all possible outputs of the operator.
    (∀ (outputVals : Vector V (Arity.ω op)),
      WellPermTypedExpr progSpec i {
        vars := (ctx.vars.removeVars args.pop.toList).insertVars rets.pop outputVals,
        perms := (ctx.perms.removeVar args.back).insertVars
          #v[rets.back]
          #v[opSpec.post op inputVals outputVals],
      } cont) →
    WellPermTypedExpr progSpec i ctx (.op (.inl (.op true op)) args rets cont)
  -- Calls to a pure operator without permission tokens.
  | wpt_op
    {args : Vector χ (Arity.ι op)}
    {rets : Vector χ (Arity.ω op + 1)}
    {inputVals : Vector V (Arity.ι op)} :
    ctx.vars.getVars args = some inputVals →
    perm = opSpec.pre op inputVals →
    -- Overapproximating all possible outputs of the operator.
    (∀ (outputVals : Vector V (Arity.ω op)),
      WellPermTypedExpr progSpec i {
        vars := (ctx.vars.removeVars args.toList).insertVars rets.pop outputVals,
        perms := ctx.perms.insertVars
          #v[rets.back]
          #v[opSpec.post op inputVals outputVals],
      } cont) →
    WellPermTypedExpr progSpec i ctx (.op (.inl (.op false op)) args rets cont)
  -- Calls to the join pseudo-operator.
  | wpt_join [NeZero k]
    {permArgs : Vector χ k}
    {depArgs : Vector χ l}
    {rets : Vector χ 2} :
    ctx.perms.getVars permArgs = some perms →
    ctx.vars.getVars depArgs = some depVals →
    PCM.add (req depVals) rem = PCM.sum perms.toList →
    WellPermTypedExpr progSpec i {
      vars := ctx.vars.removeVars depArgs.toList,
      perms := (ctx.perms.removeVars permArgs.toList).insertVars
        rets #v[req depVals, rem],
    } cont →
    WellPermTypedExpr progSpec i ctx (.op (.inl (.join k l req)) (permArgs ++ depArgs) rets cont)
  -- Calls to another function
  | wpt_call
    {j : Fin k}
    {args : Vector χ ((sigs j).ι + 1)}
    {rets : Vector χ ((sigs j).ω + 1)}
    {inputVals : Vector V (sigs j).ι} :
    (hlt : j < i) →
    ctx.vars.getVars args.pop = some inputVals →
    ctx.perms.getVar args.back = some perm →
    perm = (progSpec j).pre inputVals →
    -- Overapproximating all possible outputs of the function.
    (∀ (outputVals : Vector V (sigs j).ω),
      WellPermTypedExpr progSpec i {
        vars := (ctx.vars.removeVars args.pop.toList).insertVars rets.pop outputVals,
        perms := (ctx.perms.removeVar args.back).insertVars
          #v[rets.back] #v[(progSpec j).post outputVals],
      } cont) →
    WellPermTypedExpr progSpec i ctx
      (.op (.inr (.call (j.castLT hlt))) args rets cont)
  | wpt_br :
    WellPermTypedExpr progSpec i { ctx with vars := ctx.vars.removeVar c } left →
    WellPermTypedExpr progSpec i { ctx with vars := ctx.vars.removeVar c } right →
    WellPermTypedExpr progSpec i ctx (.br c left right)

def ProgWithSpec.WellPermTypedFn
  [Arity Op] [PCM T] [DecidableEq χ]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  (progSpec : ProgSpec V T sigs)
  (prog : ProgWithSpec χ sigs opSpec)
  (i : Fin k) : Prop :=
  ∀ args : Vector V (sigs i).ι,
    let perm := (progSpec i).pre args
    let ctx : Ctx χ V T := {
      vars := VarMap.empty.insertVars (prog i).params.pop args,
      perms := VarMap.empty.insertVars #v[(prog i).params.back] #v[perm],
    }
    ProgWithSpec.WellPermTypedExpr progSpec i ctx (prog i).body

def ProgWithSpec.WellPermTyped
  [Arity Op] [PCM T] [DecidableEq χ]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  (progSpec : ProgSpec V T sigs)
  (prog : ProgWithSpec χ sigs opSpec) : Prop :=
  ∀ i, prog.WellPermTypedFn progSpec i

/-- Well-permission-typing induces a simulation between unguarded
and guarded semantics of `Prog`. -/
theorem sim_wpt_prog
  [Arity Op]
  [InterpConsts V]
  [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  {progSpec : ProgSpec V T sigs}
  (prog : ProgWithSpec χ sigs opSpec)
  (hwt : ProgWithSpec.WellPermTyped progSpec prog)
  (i : Fin k) :
    (prog.semantics i).guard opSpec.TrivGuard
      ≲ᵣ[PreservesInit] (prog.semantics i).guard (opSpec.Guard (progSpec i))
  := by sorry

end Wavelet.Seq
