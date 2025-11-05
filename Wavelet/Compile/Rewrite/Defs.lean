import Wavelet.Dataflow.Proc
import Wavelet.Compile.MapChans

/-!
Definitions for basic optimizations on dataflow graphs.

TODO: most of these transformations are not verified yet.
-/

namespace Wavelet.Compile

open Semantics Dataflow

/-
TODOs:
[-] Expand n-ary merge/carry/steer
[-] Eliminate forwards
[ ] Eliminate dummy sinks
[ ] Eliminate dummy forks
[ ] Remove inact
-/

inductive RewriteName (χ : Type u) where
  | base (_ : χ)
  | rw (_ : RewriteName χ)
  | rename (_ : Nat) (_ : RewriteName χ)
  deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson

/--
A `Rewrite k` is roughly a function `AtomicProc^k → Option AtomicProcs`.
-/
inductive Rewrite (Op : Type u) (χ : Type v) (V : Type w) [Arity Op] : Nat → Type (max u v w) where
  | done : AtomicProcs Op (RewriteName χ) V → Rewrite Op χ V k
  | fail : Rewrite Op χ V k
  | match_on
      (f : AtomicProc Op (RewriteName χ) V → Rewrite Op χ V k) :
      Rewrite Op χ V (k + 1)

/-- Lowers n-ary async operators to unary operators. -/
def naryLowering [Arity Op] : Rewrite Op χ V 1 :=
  .match_on λ
    | .async (AsyncOp.switch k) inputs outputs =>
      if h : k > 1 ∧ inputs.length = k + 1 ∧ outputs.length = k + k then
        let hne : inputs ≠ [] := by intros h'; simp [h'] at h
        let decider := inputs.head hne
        let deciders := (List.range k).map λ i => .rename i decider
        let inputs := inputs.tail
        let outputs₁ := outputs.take k
        let outputs₂ := outputs.drop k
        .done (
          .async (.fork k) [decider] deciders ::
          (deciders |>.zip inputs |>.zip outputs₁ |>.zip outputs₂ |>.map
            (λ (((d, i), o₁), o₂) => .async (AsyncOp.switch 1) [d, i] [o₁, o₂]))
        )
      else
        .fail
    | .async (AsyncOp.merge st k) inputs outputs =>
      if h : k > 1 ∧ inputs.length = k + k + 1 ∧ outputs.length = k then
        let hne : inputs ≠ [] := by intros h'; simp [h'] at h
        let decider := inputs.head hne
        let deciders := (List.range k).map λ i => .rename i decider
        let inputs₁ := inputs.tail.take k
        let inputs₂ := inputs.tail.drop k
        .done (
          .async (.fork k) [decider] deciders ::
          (deciders |>.zip inputs₁ |>.zip inputs₂ |>.zip outputs |>.map
            (λ (((d, i₁), i₂), o) => .async (AsyncOp.merge st 1) [d, i₁, i₂] [o]))
        )
      else
        .fail
    | .async (AsyncOp.steer flavor k) inputs outputs =>
      if h : k > 1 ∧ inputs.length = k + 1 ∧ outputs.length = k then
        let hne : inputs ≠ [] := by intros h'; simp [h'] at h
        let decider := inputs.head hne
        let deciders := (List.range k).map λ i => .rename i decider
        .done (
          .async (.fork k) [decider] deciders ::
          (deciders |>.zip inputs.tail |>.zip outputs |>.map
            (λ ((d, i), o) => .async (AsyncOp.steer flavor 1) [d, i] [o]))
        )
      else
        .fail
    -- Rewrite `const v k` with a fork and `k` unary `const`s
    | .async (AsyncOp.const v k) inputs outputs =>
      if _ : k > 1 ∧ inputs.length = 1 ∧ outputs.length = k then
        let act := inputs[0]'(by omega)
        -- Copy activation signals
        let acts := outputs.mapIdx λ i _ => .rename i act
        .done (
          .async (.fork k) inputs acts ::
          (acts.zip outputs |>.map λ (act, o) => .async (AsyncOp.const v 1) [act] [o])
        )
      else
        .fail
    -- Break `forwardc` into a `forward`, a `fork`, and multiple `const`s
    | .async (AsyncOp.forwardc n m consts) inputs outputs =>
      if h : n > 0 ∧ inputs.length = n ∧ outputs.length = n + m then
        -- Take the first input as the activation signal
        -- and make `m + 1` copies (`m` for triggering the constants,
        -- and one for the original input)
        let act := inputs[0]'(by omega)
        let acts := List.range (m + 1) |>.map λ i => RewriteName.rename i act
        let outputs₁ := outputs.take n
        let outputs₂ := outputs.drop n
        .done (
          -- Forward the inputs as before
          .async (AsyncOp.forward n) (.rename 0 act :: inputs.tail) outputs₁ ::
          -- Fork the activation signals to trigger constants
          .async (.fork (m + 1)) [act] acts ::
          (consts.toList |>.zip acts.tail |>.zip outputs₂ |>.map
            λ ((c, a), o) => .async (AsyncOp.const c 1) [a] [o])
        )
      else
        .fail
    | .async (AsyncOp.forward n) inputs outputs =>
      if h : n > 1 ∧ inputs.length = n ∧ outputs.length = n then
        .done (inputs.zip outputs |>.map
          (λ (i, o) => .async (AsyncOp.forward 1) [i] [o]))
      else
        .fail
    | .async (AsyncOp.sink n) inputs outputs =>
      if h : n > 1 ∧ inputs.length = n ∧ outputs.length = 0 then
        .done (inputs.map λ i => .async (AsyncOp.sink 1) [i] [])
      else
        .fail
    | .async .inact _ _ => .done []
    | _ => .fail

/-- Optimizing combinations of steer/switch/sink/fork/forward. -/
def deadCodeElim [Arity Op] [DecidableEq χ] : Rewrite Op χ V 2 :=
  .match_on λ
    -- Forwards can be folded into either the sender or the receiver
    -- depending on which is available.
    | .async (.forward 1) inputs outputs =>
      if h : inputs.length = 1 ∧ outputs.length = 1 then
        let input := inputs[0]'(by omega)
        let output := outputs[0]'(by omega)
        .match_on λ
          | .async aop inputs' outputs' =>
            if output ∈ inputs' then
              .done [.async aop (inputs'.replace output input) outputs']
            else if input ∈ outputs' then
              .done [.async aop inputs' (outputs'.replace input output)]
            else
              .fail
          | .op op inputs' outputs' =>
            if output ∈ inputs' then
              .done [.op op (inputs'.replace output input) outputs']
            else if input ∈ outputs' then
              .done [.op op inputs' (outputs'.replace input output)]
            else
              .fail
      else
        .fail
    -- Switch with one of the outputs being a sink can be reduced to a steer
    | .async (AsyncOp.switch 1) inputs outputs =>
      if h : inputs.length = 2 ∧ outputs.length = 2 then
        let decider := inputs[0]'(by omega)
        let input := inputs[1]'(by omega)
        let output₁ := outputs[0]'(by omega)
        let output₂ := outputs[1]'(by omega)
        .match_on λ
          | .async (AsyncOp.sink 1) inputs' outputs' =>
            if h : inputs'.length = 1 ∧ outputs'.length = 0 then
              let sink := inputs'[0]'(by omega)
              if output₁ = sink then
                .done [.async (AsyncOp.steer false 1) [decider, input] [output₂]]
              else if output₂ = sink then
                .done [.async (AsyncOp.steer true 1) [decider, input] [output₁]]
              else
                .fail
            else
              .fail
          | _ => .fail
      else
        .fail
    -- Steer with a sink output can be reduced to two sinks on the decider and the input
    | .async (AsyncOp.steer flavor 1) inputs outputs =>
      if h : inputs.length = 2 ∧ outputs.length = 1 then
        let decider := inputs[0]'(by omega)
        let input := inputs[1]'(by omega)
        let output := outputs[0]'(by omega)
        .match_on λ
          | .async (AsyncOp.sink 1) inputs' outputs' =>
            if h : inputs'.length = 1 ∧ outputs'.length = 0 then
              let sink := inputs'[0]'(by omega)
              if output = sink then
                .done [
                  .async (AsyncOp.sink 1) [input] [],
                  .async (AsyncOp.sink 1) [decider] [],
                ]
              else
                .fail
            else
              .fail
          | _ => .fail
      else
        .fail
    -- -- Fork with zero outputs can be replaced with a sink (which enables further rewrites)
    -- | .async (AsyncOp.fork 0) inputs outputs =>
    --   if h : inputs.length = 1 ∧ outputs.length = 0 then
    --     .done [.async (AsyncOp.sink 1) inputs []]
    --   else
    --     .fail
    -- -- Fork with exactly one output is a forward
    -- | .async (AsyncOp.fork 1) inputs outputs =>
    --   if h : inputs.length = 1 ∧ outputs.length = 1 then
    --     .done [.async (AsyncOp.forward 1) inputs outputs]
    --   else
    --     .fail
    -- -- Fork with one of the outputs being a sink
    -- | .async (AsyncOp.fork n) inputs outputs =>
    --   if h : inputs.length = 1 ∧ outputs.length = n then
    --     let input := inputs[0]'(by omega)
    --     .match_on λ
    --       | .async (AsyncOp.sink 1) inputs' outputs' =>
    --         if h : inputs'.length = 1 ∧ outputs'.length = 0 then
    --           let sink := inputs'[0]'(by omega)
    --           if sink ∈ outputs then
    --             .done [
    --               .async (AsyncOp.fork (n - 1)) [input] (outputs.erase sink),
    --             ]
    --           else
    --             .fail
    --         else
    --           .fail
    --       | _ => .fail
    --   else
    --     .fail
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

partial def Rewrite.applyUntilFail'
  [Arity Op]
  (rw : Rewrite Op χ V k)
  (aps : AtomicProcs Op (RewriteName χ) V)
  (n : Nat) : Nat × AtomicProcs Op (RewriteName χ) V :=
  match rw.apply aps with
  | some aps' => Rewrite.applyUntilFail' rw aps' (n + 1)
  | none => (n, aps)

def Rewrite.applyUntilFail
  [Arity Op]
  (rw : Rewrite Op χ V k)
  (aps : AtomicProcs Op (RewriteName χ) V) : Nat × AtomicProcs Op (RewriteName χ) V :=
  Rewrite.applyUntilFail' rw aps 0

end Wavelet.Compile
