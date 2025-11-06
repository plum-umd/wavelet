import Wavelet.Dataflow.Proc
import Wavelet.Dataflow.Abbrev
import Wavelet.Compile.MapChans

/-!
Definitions for basic optimizations on dataflow graphs.

TODO: most of these transformations are not verified yet.
-/

namespace Wavelet.Compile

open Semantics Dataflow

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
      (f : AtomicProcs Op (RewriteName χ) V → -- Context
        AtomicProc Op (RewriteName χ) V → -- Current atom to match
        Rewrite Op χ V k) :
      Rewrite Op χ V (k + 1)

/-- Lowers n-ary async operators to unary operators. -/
def naryLowering [Arity Op] : Rewrite Op χ V 1 :=
  .match_on λ
  | ctx, .async (AsyncOp.switch k) (decider :: inputs) outputs =>
    if h : k > 1 ∧ inputs.length = k ∧ outputs.length = k + k then
      let deciders := (Vector.finRange k).map λ i => .rename i decider
      let inputs : Vector _ k := inputs.toVector.cast (by omega)
      let outputs₁ : Vector _ k := (outputs.take k).toVector.cast (by simp; omega)
      let outputs₂ : Vector _ k := (outputs.drop k).toVector.cast (by simp; omega)
      .done (
        .fork decider deciders ::
        (deciders ⊗ inputs ⊗ outputs₁ ⊗ outputs₂ |>.map
          λ ⟨d, i, o₁, o₂⟩ => .switch d #v[i] #v[o₁] #v[o₂]).toList
      )
    else
      .fail
  | ctx, .async (AsyncOp.merge st k) (decider :: inputs) outputs =>
    if h : k > 1 ∧ inputs.length = k + k ∧ outputs.length = k then
      let deciders := (Vector.finRange k).map λ i => .rename i decider
      let inputs₁ : Vector _ k := (inputs.take k).toVector.cast (by simp; omega)
      let inputs₂ : Vector _ k := (inputs.drop k).toVector.cast (by simp; omega)
      let outputs : Vector _ k := outputs.toVector.cast (by omega)
      .done (
        .fork decider deciders ::
        (deciders ⊗ inputs₁ ⊗ inputs₂ ⊗ outputs |>.map
          λ ⟨d, i₁, i₂, o⟩ => .carry st d #v[i₁] #v[i₂] #v[o]).toList
      )
    else
      .fail
  | ctx, .async (AsyncOp.steer flavor k) (decider :: inputs) outputs =>
    if h : k > 1 ∧ inputs.length = k ∧ outputs.length = k then
      let deciders := (Vector.finRange k).map λ i => .rename i decider
      let inputs : Vector _ k := inputs.toVector.cast (by omega)
      let outputs : Vector _ k := outputs.toVector.cast (by omega)
      .done (
        .fork decider deciders ::
        (deciders ⊗ inputs ⊗ outputs |>.map
          λ ⟨d, i, o⟩ => .steer flavor d #v[i] #v[o]).toList
      )
    else
      .fail
  -- Rewrite `const v k` with a fork and `k` unary `const`s
  | ctx, .async (AsyncOp.const v k) inputs outputs =>
    if _ : k > 1 ∧ inputs.length = 1 ∧ outputs.length = k then
      let act := inputs[0]'(by omega)
      -- Copy activation signals
      let acts := (Vector.finRange k).map λ i => .rename i act
      let outputs : Vector _ k := outputs.toVector.cast (by omega)
      .done (
        .fork act acts ::
        (acts ⊗ outputs |>.map λ ⟨act, o⟩ => .const v act #v[o]).toList
      )
    else
      .fail
  -- Break `forwardc` into a `forward`, a `fork`, and multiple `const`s
  | ctx, .async (AsyncOp.forwardc n m consts) inputs outputs =>
    if h : n > 0 ∧ inputs.length = n ∧ outputs.length = n + m then
      -- Take the last input as the activation signal
      -- and make `m + 1` copies (`m` for triggering the constants,
      -- and one for the original input)
      let act := inputs[n - 1]'(by omega)
      let actₘ := .rename m act
      let acts := (Vector.finRange m).map λ i => .rename i act
      let inputs : Vector _ n := (inputs.toVector.pop.push actₘ).cast (by omega)
      let outputs₁ : Vector _ n := (outputs.take n).toVector.cast (by simp; omega)
      let outputs₂ : Vector _ m := (outputs.drop n).toVector.cast (by simp; omega)
      .done (
        -- Forward the inputs as before
        .forward inputs outputs₁ ::
        -- Fork the activation signal (last input) to trigger constants
        .fork act (acts.push actₘ) ::
        (consts ⊗ acts ⊗ outputs₂ |>.map
          λ ⟨v, a, o⟩ => .const v a #v[o]).toList
      )
    else
      .fail
  | ctx, .async (AsyncOp.forward n) inputs outputs =>
    if h : n > 1 ∧ inputs.length = n ∧ outputs.length = n then
      let inputs : Vector _ n := inputs.toVector.cast (by omega)
      let outputs : Vector _ n := outputs.toVector.cast (by omega)
      .done (inputs ⊗ outputs |>.map λ ⟨i, o⟩ => .forward #v[i] #v[o]).toList
    else
      .fail
  | ctx, .async (AsyncOp.sink n) inputs outputs =>
    if h : n > 1 ∧ inputs.length = n ∧ outputs.length = 0 then
      let inputs : Vector _ n := inputs.toVector.cast (by omega)
      .done (inputs.map λ i => .sink #v[i]).toList
    else
      .fail
  | ctx, .async .inact _ _ => .done []
  | _, _ => .fail

/-- Checks if the given two channels are output of the same fork. -/
def outputsOfSameFork
  [Arity Op] [DecidableEq χ]
  (aps : AtomicProcs Op (RewriteName χ) V)
  (chan₁ chan₂ : RewriteName χ) : Bool :=
  aps.any λ
  | .async (AsyncOp.fork _) _ outputs =>
    chan₁ ∈ outputs ∧ chan₂ ∈ outputs
  | _ => false

/-- Optimizing combinations of steer/switch/sink/fork/forward. -/
def deadCodeElim [Arity Op] [DecidableEq χ] [InterpConsts V] : Rewrite Op χ V 3 :=
  .match_on λ
  -- Forwards can be folded into either the sender or the receiver
  -- depending on which is available.
  | ctx, .async (.forward 1) inputs outputs =>
    if h : inputs.length = 1 ∧ outputs.length = 1 then
      let input := inputs[0]'(by omega)
      let output := outputs[0]'(by omega)
      .match_on λ
      | ctx, .async aop inputs' outputs' =>
        if output ∈ inputs' then
          .done [.async aop (inputs'.replace output input) outputs']
        else if input ∈ outputs' then
          .done [.async aop inputs' (outputs'.replace input output)]
        else
          .fail
      | ctx, .op op inputs' outputs' =>
        if output ∈ inputs' then
          .done [.op op (inputs'.replace output input) outputs']
        else if input ∈ outputs' then
          .done [.op op inputs' (outputs'.replace input output)]
        else
          .fail
    else
      .fail
  | ctx, .async (AsyncOp.switch 1) inputs outputs =>
    if h : inputs.length = 2 ∧ outputs.length = 2 then
      let decider := inputs[0]'(by omega)
      let input := inputs[1]'(by omega)
      let output₁ := outputs[0]'(by omega)
      let output₂ := outputs[1]'(by omega)
      .match_on λ
      -- Switch with one of the outputs being a sink can be reduced to a steer
      | ctx, .async (AsyncOp.sink 1) inputs' outputs' =>
        if h : inputs'.length = 1 ∧ outputs'.length = 0 then
          let sink := inputs'[0]'(by omega)
          if output₁ = sink then
            .done [.steer false decider #v[input] #v[output₂]]
          else if output₂ = sink then
            .done [.steer true decider #v[input] #v[output₁]]
          else
            .fail
        else
          .fail
      | _, _ => .fail
    else
      .fail
  | ctx, .async (AsyncOp.steer flavor 1) inputs outputs =>
    if h : inputs.length = 2 ∧ outputs.length = 1 then
      let decider := inputs[0]'(by omega)
      let input := inputs[1]'(by omega)
      let output := outputs[0]'(by omega)
      .match_on λ
      -- Steer with a sink output can be reduced to two sinks on the decider and the input
      | ctx, .async (AsyncOp.sink 1) inputs' outputs' =>
        if h : inputs'.length = 1 ∧ outputs'.length = 0 then
          let sink := inputs'[0]'(by omega)
          if output = sink then
            .done [
              .sink #v[input],
              .sink #v[decider],
            ]
          else
            .fail
        else
          .fail
      -- Two consecutive steers with the same flavor and same decider can be folded
      | ctx, .async (AsyncOp.steer flavor' 1) inputs' outputs' =>
        if h : inputs'.length = 2 ∧ outputs'.length = 1 then
          let decider' := inputs'[0]'(by omega)
          let input' := inputs'[1]'(by omega)
          let output' := outputs'[0]'(by omega)
          if flavor = flavor' ∧ output = input' ∧ outputsOfSameFork ctx decider decider' then
            .done [
              .steer flavor decider #v[input] #v[output'],
              .sink #v[decider'],
            ]
          else
            .fail
        else
          .fail
      | _, _ => .fail
    else
      .fail
  -- Fork with zero outputs can be replaced with a sink (which enables further rewrites)
  | ctx, .async (AsyncOp.fork 0) inputs outputs =>
    if h : inputs.length = 1 ∧ outputs.length = 0 then
      .done [.sink inputs.toVector]
    else
      .fail
  -- Fork with exactly one output is a forward
  | ctx, .async (AsyncOp.fork 1) inputs outputs =>
    if h : inputs.length = 1 ∧ outputs.length = 1 then
      .done [.forward #v[inputs[0]] #v[outputs[0]]]
    else
      .fail
  -- Fork with one of the outputs being a sink or another fork
  | ctx, .async (AsyncOp.fork n) inputs outputs =>
    if h : inputs.length = 1 ∧ outputs.length = n then
      let input := inputs[0]'(by omega)
      .match_on λ
      | ctx, .async (AsyncOp.sink 1) inputs' outputs' =>
        if h : inputs'.length = 1 ∧ outputs'.length = 0 then
          let sink := inputs'[0]'(by omega)
          if sink ∈ outputs then
            .done [
              .fork input (outputs.erase sink).toVector,
            ]
          else
            .fail
        else
          .fail
      -- Folding two consecutive forks
      | ctx, .async (AsyncOp.fork m) inputs' outputs' =>
        if h : inputs'.length = 1 ∧ outputs'.length = m then
          let input' := inputs'[0]'(by omega)
          if input' ∈ outputs then
            .done [
              .fork input (outputs.erase input' ++ outputs').toVector,
            ]
          else
          .fail
        else
          .fail
      | _, _ => .fail
    else
      .fail
  -- Order with one input can be rewritten to a forward
  | ctx, .async (AsyncOp.order 1) inputs outputs =>
    if h : inputs.length = 1 ∧ outputs.length = 1 then
      let input := inputs[0]'(by omega)
      let output := outputs[0]'(by omega)
      .done [.forward #v[input] #v[output]]
    else
      .fail
  -- Constant with a sink output can be rewritten to a sink
  | ctx, .async (AsyncOp.const v 1) inputs outputs =>
    if h : inputs.length = 1 ∧ outputs.length = 1 then
      let act := inputs[0]'(by omega)
      let output := outputs[0]'(by omega)
      .match_on λ
      | ctx, .async (AsyncOp.sink 1) inputs' outputs' =>
        if h : inputs'.length = 1 ∧ outputs'.length = 0 then
          let sink := inputs'[0]'(by omega)
          if output = sink then
            .done [.sink #v[act]]
          else
            .fail
        else
          .fail
      | _, _ => .fail
    else
      .fail
  -- TODO: these rewrites might be a bit risky and may change deadlock behavior
  | ctx, .async (AsyncOp.merge .decider 1) inputs outputs =>
    if h : inputs.length = 3 ∧ outputs.length = 1 then
      let decider := inputs[0]'(by omega)
      let inputL := inputs[1]'(by omega)
      let inputR := inputs[2]'(by omega)
      let output := outputs[0]'(by omega)
      .match_on λ
      -- Merge -> steer can be optimized to a steer and a sink
      -- if they have the same decider (both deciders coming from a fork)
      | ctx, .async (AsyncOp.steer flavor 1) inputs' outputs' =>
        if h : inputs'.length = 2 ∧ outputs'.length = 1 then
          let decider' := inputs'[0]'(by omega)
          let input' := inputs'[1]'(by omega)
          let output' := outputs'[0]'(by omega)
          if output = input' ∧ outputsOfSameFork ctx decider decider' then
            if flavor then
              .done [
                -- Pass RHS (true side) through and sink LHS (false side)
                .steer true decider #v[inputR] #v[output'],
                .sink #v[decider'],
                .sink #v[inputL],
              ]
            else
              .done [
                -- Pass LHS (false side) through and sink RHS (true side)
                .steer false decider #v[inputL] #v[output'],
                .sink #v[decider'],
                .sink #v[inputR],
              ]
          else
            .fail
        else
          .fail
      -- Merge in the decider state with a constant false LHS and constant true RHS
      -- can be rewritten to a forward from the decider
      | ctx, .async (AsyncOp.const (V := V) v₁ 1) inputs₁ outputs₁ =>
        .match_on λ
        | ctx, .async (AsyncOp.const (V := V) v₂ 1) inputs₂ outputs₂ =>
          if h₁ : inputs₁.length = 1 ∧ outputs₁.length = 1 ∧
            inputs₂.length = 1 ∧ outputs₂.length = 1 then
            let outputs₁ := outputs₁[0]'(by omega)
            let outputs₂ := outputs₂[0]'(by omega)
            if inputL = outputs₁ ∧ inputR = outputs₂ ∧
              InterpConsts.toBool v₁ = some false ∧
              InterpConsts.toBool v₂ = some true then
              .done [
                .forward #v[decider] #v[output],
                .sink #v[inputs₁[0]'(by omega)],
                .sink #v[inputs₂[0]'(by omega)],
              ]
            else
              .fail
          else
            .fail
        | _, _ => .fail
      | _, _ => .fail
    else
      .fail
  | _, _ => .fail

/--
TODO: This is quite inefficient (e.g., doing pattern matching on a graph with n nodes will take O(n^k).)
Implement a proper graph rewriting algorithm in the future.
-/
def Rewrite.applyAtoms [Arity Op]
  (rw : Rewrite Op χ V k)
  (aps : AtomicProcs Op (RewriteName χ) V) : Option (AtomicProcs Op (RewriteName χ) V) :=
  match rw with
  | .done aps' => some ((aps ++ aps').mapChans .rw) -- Rename after each rewrite to avoid future name clashes
  | .fail => none
  | .match_on f =>
    aps.mapIdx (λ i ap =>
      -- Remove the matched atomic proc and continue matching
      let ctx := aps.take i ++ aps.drop (i + 1)
      (f ctx ap, ctx))
    |>.firstM λ (rw', rest) => rw'.applyAtoms rest

def Rewrite.apply [Arity Op]
  (rw : Rewrite Op χ V k)
  (proc : Proc Op (RewriteName χ) V m n) : Option (Proc Op (RewriteName χ) V m n) :=
  return {
    inputs := proc.inputs.map .rw,
    outputs := proc.outputs.map .rw,
    atoms := ← rw.applyAtoms proc.atoms,
  }

partial def Rewrite.applyUntilFail'
  [Arity Op]
  (rw : Rewrite Op χ V k)
  (proc : Proc Op (RewriteName χ) V m n)
  (numRewrites : Nat) : Nat × Proc Op (RewriteName χ) V m n :=
  match rw.apply proc with
  | some proc' => Rewrite.applyUntilFail' rw proc' (numRewrites + 1)
  | none => (numRewrites, proc)

def Rewrite.applyUntilFail
  [Arity Op]
  (rw : Rewrite Op χ V k)
  (proc : Proc Op (RewriteName χ) V m n) : Nat × Proc Op (RewriteName χ) V m n :=
  Rewrite.applyUntilFail' rw proc 0

end Wavelet.Compile
