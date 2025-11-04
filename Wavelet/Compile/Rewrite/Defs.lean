import Wavelet.Dataflow.Proc
import Wavelet.Compile.MapChans

/-!
Definitions for basic optimizations on dataflow graphs.

TODO: most of these transformations are not verified yet.
-/

namespace Wavelet.Compile

open Semantics Dataflow

/-
Plan:
- Expand n-ary merge/carry/steer
- Eliminate forwards
- Eliminate dummy sinks
- Eliminate dummy forks
- Remove inact
-/

inductive RewriteName (χ : Type u) where
  | base (_ : χ)
  | rw (_ : RewriteName χ)
  | rename (_ : Nat) (_ : RewriteName χ)
  deriving Repr, Lean.ToJson, Lean.FromJson

/--
A `Rewrite k` is roughly a function `AtomicProc^k → Option AtomicProcs`.
-/
inductive Rewrite (Op : Type u) (χ : Type v) (V : Type w) [Arity Op] : Nat → Type (max u v w) where
  | done : AtomicProcs Op (RewriteName χ) V → Rewrite Op χ V 0
  | fail : Rewrite Op χ V k
  | match_on
      (f : AtomicProc Op (RewriteName χ) V → Rewrite Op χ V k) :
      Rewrite Op χ V (k + 1)

/-- Lower n-ary async operators to unary operators -/
def naryLowering [Arity Op] : Rewrite Op χ V 1 :=
  .match_on λ
    | .async (AsyncOp.switch k) inputs outputs =>
      if h : k > 1 ∧ inputs.length = k + 1 ∧ outputs.length = k + k then
        let hne : inputs ≠ [] := by intros h'; simp [h'] at h
        let decider := inputs.head hne
        let inputs := inputs.tail
        let outputs₁ := outputs.take k
        let outputs₂ := outputs.drop k
        .done ((inputs.zip outputs₁).zip outputs₂ |>.map
          (λ ((i, o₁), o₂) => .async (AsyncOp.switch 1) [decider, i] [o₁, o₂]))
      else
        .fail
    | .async (AsyncOp.merge st k) inputs outputs =>
      if k > 1 ∧ inputs.length = k ∧ outputs.length = k then
        .done (inputs.zip outputs |>.map
          (λ (i, o) => .async (AsyncOp.merge st 1) [i] [o]))
      else
        .fail
    | .async (AsyncOp.steer flavor k) inputs outputs =>
      if h : k > 1 ∧ inputs.length = k + 1 ∧ outputs.length = k then
        let hne : inputs ≠ [] := by intros h'; simp [h'] at h
        .done (inputs.tail.tail.zip outputs |>.map
          (λ (i, o) => .async (AsyncOp.steer flavor 1) [inputs.head hne, i] [o]))
      else
        .fail

    | .async (AsyncOp.const v k) inputs outputs =>
      if _ : k > 1 ∧ inputs.length = 1 ∧ outputs.length = k then
        let act := inputs[0]'(by omega)
        -- Copy activation signals
        let acts := outputs.mapIdx λ i _ => .rename i act
        .done (
          .async (AsyncOp.fork 1) inputs acts ::
          (acts.zip outputs |>.map λ (act, o) => .async (AsyncOp.const v 1) [act] [o])
        )
      else
        .fail
    | _ => .fail

/--
TODO: This is quite inefficient (e.g., doing pattern matching on a graph with n nodes will take O(n^k).)
Implement a proper graph rewriting algorithm in the future.
-/
def Rewrite.apply [Arity Op]
  (rw : Rewrite Op χ V k)
  (aps : AtomicProcs Op (RewriteName χ) V) : Option (AtomicProcs Op (RewriteName χ) V) :=
  match rw with
  | .done aps' => some ((aps ++ aps').mapChans .rw) -- Rename after each rewrite to avoid future name clashes
  | .fail => none
  | .match_on f =>
    aps.mapIdx (λ i ap => (i, f ap)) |>.firstM λ (i, rw') =>
      -- Remove the matched atomic proc and continue matching
      rw'.apply (aps.take i ++ aps.drop (i + 1))

partial def Rewrite.applyUntilFail
  [Arity Op]
  (rw : Rewrite Op χ V k)
  (aps : AtomicProcs Op (RewriteName χ) V) : AtomicProcs Op (RewriteName χ) V :=
  match rw.apply aps with
  | some aps' => Rewrite.applyUntilFail rw aps'
  | none => aps

end Wavelet.Compile
