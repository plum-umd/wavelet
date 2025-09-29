import Wavelet.Seq

namespace Wavelet.Seq

open Op

universe u v w

/-- Base types for l0. Instances of this class
    provide at least a distinguished boolean type. One can extend
    `τ` with further constructors (e.g. integers, units) by
    defining an appropriate instance of `BaseTy`. -/
class BaseTy (τ : Type w) where
  boolTy : τ

/-- Given an operator set `Op`, an `OpTy` instance assigns to each
    operator `o : Op` a vector of input types of length `Arity.ι o`
    and a vector of output types of length `Arity.ω o`. -/
class OpTy (τ : Type w) (Op : Type v) [Arity Op] where
  inputTypes  : (o : Op) → Vector τ (Arity.ι o)
  outputTypes : (o : Op) → Vector τ (Arity.ω o)

abbrev TyEnv (χ : Type u) (τ : Type w) := χ → Option τ

namespace TyEnv

variable {χ : Type u} {τ : Type w}

/-- The empty type environment with no bindings. -/
def empty : TyEnv χ τ := λ _ => none

/-- Insert a vector of variables together with a vector of types into
    an existing environment. -/
def insertVars [DecidableEq χ]
    {n : Nat} (vars : Vector χ n) (tys : Vector τ n)
    (Γ : TyEnv χ τ) : TyEnv χ τ :=
  λ v =>
    ((vars.zip tys).toList.find? (·.1 = v)).map (·.2) <|> Γ v

/-- Remove a single variable from the environment. -/
def removeVar [DecidableEq χ] (x : χ) (Γ : TyEnv χ τ) : TyEnv χ τ :=
  λ y => if y = x then none else Γ y

/-- Remove a list of variables from the environment. -/
def removeVars [DecidableEq χ] (xs : List χ) (Γ : TyEnv χ τ) : TyEnv χ τ :=
  λ y => if y ∈ xs then none else Γ y

/-- Lookup the type of a variable in the environment. -/
def getVar (Γ : TyEnv χ τ) (x : χ) : Option τ := Γ x

/-- Well-typed variables -/
def wellTypedVars [DecidableEq χ]
    (vars : Vector χ n) (tys : Vector τ n) (Γ : TyEnv χ τ) : Prop :=
  List.Forall₂ (λ v ty => Γ.getVar v = some ty) vars.toList tys.toList

end TyEnv

/-- Typing judgement for expressions. -/
inductive Expr.Typed
    [Arity Op] [BaseTy τ] [OpTy τ Op] [DecidableEq χ] :
    TyEnv χ τ → Expr Op χ m n → Vector τ m → Vector τ n → Prop
  | ret
      {vars : Vector χ n} {inTys: Vector τ m} {outTys : Vector τ n}:
      Γ.wellTypedVars vars outTys →
      Expr.Typed Γ (.ret vars) inTys outTys
  | tail
      {vars : Vector χ m} {inTys: Vector τ m} {outTys : Vector τ n}:
      Γ.wellTypedVars vars inTys →
      Expr.Typed Γ (.tail vars) inTys outTys
  | op
      {args : Vector χ (Arity.ι o)} {rets : Vector χ (Arity.ω o)}
      {inTys : Vector τ m} {outTys : Vector τ n}:
      Γ.wellTypedVars args (OpTy.inputTypes o) →
      Expr.Typed (Γ.insertVars rets (OpTy.outputTypes o)) cont inTys outTys →
      Expr.Typed Γ (.op o args rets cont) inTys outTys
  | br {cond : χ}
      {inTys : Vector τ m} {outTys : Vector τ n}:
      TyEnv.getVar Γ cond = some (BaseTy.boolTy) →
      Expr.Typed Γ left inTys outTys →
      Expr.Typed Γ right inTys outTys →
      Expr.Typed Γ (.br cond left right) inTys outTys

def Fn.Typed
    [BaseTy τ] [Arity Op] [OpTy τ Op] [DecidableEq χ] :
    Fn Op χ m n → Vector τ m → Vector τ n → Prop
  | ⟨params, body⟩, inTys, outTys =>
      let Γ₀ := TyEnv.insertVars params inTys TyEnv.empty
      Expr.Typed Γ₀ body inTys outTys

end Wavelet.Seq
