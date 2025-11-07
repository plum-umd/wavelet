import Wavelet.Data.List
import Wavelet.Data.Vector

import Wavelet.Dataflow.Proc
import Wavelet.Dataflow.Abbrev

import Wavelet.Compile.MapChans
import Wavelet.Compile.Rewrite.Rename

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
  deriving Repr, Hashable, DecidableEq, Lean.ToJson, Lean.FromJson

structure RewriteState Op χ V [Arity Op] [DecidableEq χ] [Hashable χ] where
  aps : AtomicProcs Op (RewriteName χ) V
  chanToAtoms : Std.HashMap (RewriteName χ) (List (Fin aps.length))
  matched : List Nat

def RewriteState.buildChanToAtomsMap [Arity Op] [DecidableEq χ] [Hashable χ]
  (aps : AtomicProcs Op (RewriteName χ) V) :
    Std.HashMap (RewriteName χ) (List (Fin aps.length)) :=
  List.finRange aps.length
    |>.foldl
      (λ m i => m
        |> aps[i].inputs.foldl (λ m name => m.insert name (i :: m.getD name []))
        |> aps[i].outputs.foldl (λ m name => m.insert name (i :: m.getD name [])))
      (Std.HashMap.emptyWithCapacity (2 * aps.length))

def RewriteState.init [Arity Op] [DecidableEq χ] [Hashable χ]
  (aps : AtomicProcs Op (RewriteName χ) V) : RewriteState Op χ V :=
  {
    aps,
    -- Builds a map from channel names to "related" atom indices
    -- for faster lookup.
    chanToAtoms := buildChanToAtomsMap aps,
    matched := []
  }

abbrev RewriteM Op χ V [Arity Op] [DecidableEq χ] [Hashable χ] :=
  StateT (RewriteState Op χ V) Option

abbrev Rewrite Op χ V [Arity Op] [DecidableEq χ] [Hashable χ] :=
  RewriteM Op χ V (AtomicProcs Op (RewriteName χ) V)

def RewriteM.apply [Arity Op] [DecidableEq χ] [Hashable χ]
  (rw : RewriteM Op χ V (AtomicProcs Op (RewriteName χ) V))
  (proc : Proc Op (RewriteName χ) V m n) :
    Option (Proc Op (RewriteName χ) V m n) := do
  let (aps', s) ← rw.run (.init proc.atoms)
  let unmatched := s.aps.mapIdx (·, ·)
    |>.filter (λ (i, _) => i ∉ s.matched)
    |>.map (·.snd)
  -- Final renaming to avoid name conflicts in the future
  return {
    inputs := proc.inputs.map .rw,
    outputs := proc.outputs.map .rw,
    atoms := AtomicProcs.mapChans .rw (aps' ++ unmatched)
  }

/-- Apply the given rewrite until failure. -/
partial def Rewrite.applyUntilFail
  [Arity Op] [DecidableEq χ] [Hashable χ]
  (rw : Rewrite Op χ V)
  (proc : Proc Op (RewriteName χ) V m n) : Nat × Proc Op (RewriteName χ) V m n :=
    loop 0 proc
  where
    loop numRewrites proc : Nat × Proc Op (RewriteName χ) V m n :=
      match rw.apply proc with
      | some proc' => loop (numRewrites + 1) proc'
      | none => (numRewrites, proc)

/-- Similar to `applyUntilFail` but performs `renameChans` every round
for slightly better performance. -/
partial def Rewrite.applyUntilFailNat
  [Arity Op] [DecidableEq χ]
  (rw : Rewrite Op Nat V)
  (proc : Proc Op χ V m n) : Nat × Proc Op Nat V m n :=
    loop 0 proc.renameChans
  where
    loop numRewrites proc : Nat × Proc Op Nat V m n :=
      match rw.apply (proc.mapChans .base) with
      | some proc' => loop (numRewrites + 1) proc'.renameChans
      | none => (numRewrites, proc.renameChans)

/--
Tries to match every atomic proc in the context with the continuation,
and returns the first with non-failure result.

TODO: This is quite inefficient (e.g., doing pattern matching on a graph with n nodes will take O(n^k).)
Implement a proper graph rewriting algorithm in the future.
-/
@[always_inline]
def RewriteM.choose [Arity Op] [DecidableEq χ] [Hashable χ]
  (cont : AtomicProc Op (RewriteName χ) V → RewriteM Op χ V α) :
    RewriteM Op χ V α
  := do
  let s ← get
  (List.finRange s.aps.length).filter (↑· ∉ s.matched)
    |>.firstM λ i : Fin _ => do
      -- dbg_trace s!"rewriting depth {s.matched.length}, index {i}"
      set { s with matched := i :: s.matched }
      cont s.aps[i]

/-- Choose only atoms that are "relevant" to the given names,
i.e., the name is either an input or output of the atom. -/
@[always_inline]
def RewriteM.chooseNames [Arity Op] [DecidableEq χ] [Hashable χ]
  (names : List (RewriteName χ))
  (cont : AtomicProc Op (RewriteName χ) V → RewriteM Op χ V α) :
    RewriteM Op χ V α
  := do
  let s ← get
  names.map (s.chanToAtoms.getD · [])
    |>.firstM λ ids => ids.filter (↑· ∉ s.matched)
    |>.firstM λ i : Fin _ => do
      -- dbg_trace s!"rewriting depth {s.matched.length}, index {i}"
      set { s with matched := i :: s.matched }
      cont s.aps[i]

@[always_inline]
def RewriteM.assume [Arity Op] [DecidableEq χ] [Hashable χ]
  (p : Prop) [Decidable p]
  (cont : p → RewriteM Op χ V α) : RewriteM Op χ V α :=
  if h : p then
    cont h
  else
    failure

@[always_inline]
def RewriteM.ctx [Arity Op] [DecidableEq χ] [Hashable χ] :
    RewriteM Op χ V (AtomicProcs Op (RewriteName χ) V) := do
  let s ← get
  return s.aps.mapIdx (·, ·)
    |>.filter (λ (i, _) => i ∉ s.matched)
    |>.map (·.snd)

/-- Gets the list of operators that reference the give names in the context. -/
@[always_inline]
def RewriteM.ctxWithNames [Arity Op] [DecidableEq χ] [Hashable χ]
  (names : List (RewriteName χ)) :
    RewriteM Op χ V (AtomicProcs Op (RewriteName χ) V) := do
  let s ← get
  return names.map (s.chanToAtoms.getD · [])
    |>.flatten
    |>.filter (↑· ∉ s.matched)
    |>.map (s.aps[·])

/-- Checks if the given two channels are output of the same fork. -/
@[always_inline]
def RewriteM.assumeFromSameFork
  [Arity Op] [DecidableEq χ] [Hashable χ]
  (chan₁ chan₂ : RewriteName χ) :
    RewriteM Op χ V Unit := do
  (← .ctxWithNames [chan₁, chan₂]).firstM λ
  | .async (AsyncOp.fork _) _ outputs =>
    if chan₁ ∈ outputs ∧ chan₂ ∈ outputs then
      return ()
    else failure
  | _ => failure

/-- Checks if a channel is the output of a constant gate, modulo one or no forks
(since multiple forks will be combined). -/
def RewriteM.checkFromConst
  [Arity Op] [DecidableEq χ] [Hashable χ]
  (chan : RewriteName χ) :
    RewriteM Op χ V V := do
  (← .ctxWithNames [chan]).firstM λ
  | .async (AsyncOp.fork _) inputs outputs =>
    .assume (inputs.length = 1) λ h => do
    let input := inputs[0]'(by omega)
    if chan ∈ outputs then
      -- Continue searching through the outputs of the fork
      (← .ctxWithNames [input]).firstM λ
      | .async (.const v k) _ outputs =>
        if input ∈ outputs then
          return v
        else failure
      | _ => failure
    else failure
  | .async (.const v k) _ outputs =>
    if chan ∈ outputs then return v
    else failure
  | _ => failure

/-- Lowers n-ary async operators to unary operators. -/
def naryLowering [Arity Op] [DecidableEq χ] [Hashable χ] :
    Rewrite Op χ V :=
  .choose λ
  | .async (AsyncOp.switch k) (decider :: inputs) outputs =>
    .assume (k > 1) λ h => do
    let deciders := (Vector.finRange k).map (.rename · decider)
    let inputs ← inputs.toVectorDyn k
    let outputs₁ ← (outputs.take k).toVectorDyn k
    let outputs₂ ← (outputs.drop k).toVectorDyn k
    return .fork decider deciders ::
      (deciders ⊗ inputs ⊗ outputs₁ ⊗ outputs₂ |>.map
        λ ⟨d, i, o₁, o₂⟩ => .switch d #v[i] #v[o₁] #v[o₂]).toList
  | .async (AsyncOp.merge st k) (decider :: inputs) outputs =>
    .assume (k > 1) λ h => do
    let deciders := (Vector.finRange k).map (.rename · decider)
    let inputs₁ ← (inputs.take k).toVectorDyn k
    let inputs₂ ← (inputs.drop k).toVectorDyn k
    let outputs ← outputs.toVectorDyn k
    return .fork decider deciders ::
      (deciders ⊗ inputs₁ ⊗ inputs₂ ⊗ outputs |>.map
        λ ⟨d, i₁, i₂, o⟩ => .carry st d #v[i₁] #v[i₂] #v[o]).toList
  | .async (AsyncOp.steer flavor k) (decider :: inputs) outputs =>
    .assume (k > 1) λ h => do
    let deciders := (Vector.finRange k).map (.rename · decider)
    let inputs ← inputs.toVectorDyn k
    let outputs ← outputs.toVectorDyn k
    return .fork decider deciders ::
      (deciders ⊗ inputs ⊗ outputs |>.map
        λ ⟨d, i, o⟩ => .steer flavor d #v[i] #v[o]).toList
  -- Rewrite `const v k` with a fork and `k` unary `const`s
  | .async (AsyncOp.const v k) inputs outputs =>
    .assume (k > 1 ∧ inputs.length = 1 ∧ outputs.length = k) λ h => do
    let act := inputs[0]'(by omega)
    -- Copy activation signals
    let acts := (Vector.finRange k).map (.rename · act)
    let outputs : Vector _ k := outputs.toVector.cast (by omega)
    return .fork act acts ::
      (acts ⊗ outputs |>.map λ ⟨act, o⟩ => .const v act #v[o]).toList
  -- Break `forwardc` into a `forward`, a `fork`, and multiple `const`s
  | .async (AsyncOp.forwardc n m consts) inputs outputs =>
    .assume (n > 0 ∧ inputs.length = n ∧ outputs.length = n + m) λ h => do
    -- Take the last input as the activation signal
    -- and make `m + 1` copies (`m` for triggering the constants,
    -- and one for the original input)
    let act := inputs[n - 1]'(by omega)
    let actₘ := .rename m act
    let acts := (Vector.finRange m).map λ i => .rename i act
    let inputs : Vector _ n := (inputs.toVector.pop.push actₘ).cast (by omega)
    let outputs₁ : Vector _ n := (outputs.take n).toVector.cast (by simp; omega)
    let outputs₂ : Vector _ m := (outputs.drop n).toVector.cast (by simp; omega)
    return (
      -- Forward the inputs as before
      .forward inputs outputs₁ ::
      -- Fork the activation signal (last input) to trigger constants
      .fork act (acts.push actₘ) ::
      (consts ⊗ acts ⊗ outputs₂ |>.map
        λ ⟨v, a, o⟩ => .const v a #v[o]).toList
    )
  | .async (AsyncOp.forward n) inputs outputs =>
    .assume (n > 1 ∧ inputs.length = n ∧ outputs.length = n) λ h => do
    let inputs : Vector _ n := inputs.toVector.cast (by omega)
    let outputs : Vector _ n := outputs.toVector.cast (by omega)
    return (inputs ⊗ outputs |>.map λ ⟨i, o⟩ => .forward #v[i] #v[o]).toList
  | .async (AsyncOp.sink n) inputs outputs =>
    .assume (n > 1 ∧ inputs.length = n ∧ outputs.length = 0) λ h => do
    let inputs : Vector _ n := inputs.toVector.cast (by omega)
    return (inputs.map λ i => .sink #v[i]).toList
  | .async (.inact 0) _ _ => return []
  | _ => failure

/-- Optimizing combinations of steer/switch/sink/fork/forward. -/
def deadCodeElim [Arity Op] [DecidableEq χ] [Hashable χ] [InterpConsts V] :
    Rewrite Op χ V :=
  .choose λ
  -- Forwards can be folded into either the sender or the receiver
  -- depending on which is available.
  | .async (.forward 1) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    let input := inputs[0]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseNames [input, output] λ
    | .async aop inputs' outputs' => do
      if output ∈ inputs' then
        return [.async aop (inputs'.replace output input) outputs']
      else if input ∈ outputs' then
        return [.async aop inputs' (outputs'.replace input output)]
      else failure
    | .op op inputs' outputs' => do
      if output ∈ inputs' then
        return [.op op (inputs'.replace output input) outputs']
      else if input ∈ outputs' then
        return [.op op inputs' (outputs'.replace input output)]
      else failure
  | .async (.switch 1) inputs outputs =>
    .assume (inputs.length = 2 ∧ outputs.length = 2) λ h => do
    let decider := inputs[0]'(by omega)
    let input := inputs[1]'(by omega)
    let output₁ := outputs[0]'(by omega)
    let output₂ := outputs[1]'(by omega)
    .chooseNames [output₁, output₂] λ
    -- Switch with one of the outputs being a sink can be reduced to a steer
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if output₁ = sink then
        return [.steer false decider #v[input] #v[output₂]]
      else if output₂ = sink then
        return [.steer true decider #v[input] #v[output₁]]
      else failure
    | _ => failure
  | .async (.steer flavor 1) inputs outputs =>
    .assume (inputs.length = 2 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let input := inputs[1]'(by omega)
    let output := outputs[0]'(by omega)
    -- Steer with decider coming from a constant can be replaced with a sink or order
    (do
      let val ← .checkFromConst decider
      if let some val := InterpConsts.toBool val then
        if val = flavor then
          return [.order #v[decider, input] output]
        else
          return [
            .sink #v[input],
            .sink #v[decider],
            .inact #v[output],
          ]
      failure) <|>
    .chooseNames (inputs ++ outputs) λ
    -- Steer with a sink output can be reduced to two sinks on the decider and the input
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if output = sink then
        return [
          .sink #v[input],
          .sink #v[decider],
        ]
      else failure
    -- Two consecutive steers with the same flavor and same decider can be folded
    | .async (.steer flavor' 1) inputs' outputs' =>
      .assume (inputs'.length = 2 ∧ outputs'.length = 1) λ h => do
      let decider' := inputs'[0]'(by omega)
      let input' := inputs'[1]'(by omega)
      let output' := outputs'[0]'(by omega)
      .assumeFromSameFork decider decider'
      if flavor = flavor' ∧ output = input' then
        return [
          .steer flavor decider #v[input] #v[output'],
          .sink #v[decider'],
        ]
      else failure
    | _ => failure
  -- Fork with zero outputs can be replaced with a sink (which enables further rewrites)
  | .async (.fork 0) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = 0) λ h => do
    return [.sink inputs.toVector]
  -- Fork with exactly one output is a forward
  | .async (.fork 1) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    return [.forward #v[inputs[0]] #v[outputs[0]]]
  -- Fork with one of the outputs being a sink or another fork
  | .async (.fork n) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = n) λ h => do
    let input := inputs[0]'(by omega)
    .chooseNames (inputs ++ outputs) λ
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if sink ∈ outputs then
        return [.fork input (outputs.erase sink).toVector]
      else failure
    -- Folding two consecutive forks
    | .async (.fork m) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = m) λ h => do
      let input' := inputs'[0]'(by omega)
      if input' ∈ outputs then
        return [.fork input (outputs.erase input' ++ outputs').toVector]
      else failure
    | _ => failure
  -- Order with one input can be rewritten to a forward
  | .async (.order 1) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    let input := inputs[0]'(by omega)
    let output := outputs[0]'(by omega)
    return [.forward #v[input] #v[output]]
  -- Constant with a sink output can be rewritten to a sink
  | .async (.const v 1) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    let act := inputs[0]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseNames (inputs ++ outputs) λ
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if output = sink then
        return [.sink #v[act]]
      else failure
    | _ => failure
  | .async (.inact n) inputs outputs =>
    .assume (n > 0 ∧ inputs.length = 0 ∧ outputs.length = n) λ h => do
    .chooseNames outputs λ
    -- Inact + sink : the channel between them can be removed
    | .async (AsyncOp.sink m) inputs' outputs' =>
      .assume (inputs'.length = m ∧ outputs'.length = 0) λ h => do
      if ¬ outputs.Disjoint inputs' then
        return [
          .inact (outputs.removeAll inputs').toVector,
          .sink (inputs'.removeAll outputs).toVector,
        ]
      else failure
    | _ => failure
  -- Carry (true flavor) with a constant false decider
  | .async (.merge .popLeft 1) inputs outputs =>
    .assume (inputs.length = 3 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let inputL := inputs[1]'(by omega)
    let inputR := inputs[2]'(by omega)
    let output := outputs[0]'(by omega)
    let val ← .checkFromConst decider
    if let some val := InterpConsts.toBool val then
      if ¬val then
        -- The right input is never consumed
        return [
          .forward #v[inputL] #v[output],
          .sink #v[decider],
          .sink #v[inputR],
        ]
    failure
  -- Carry (false flavor) with a constant true decider
  | .async (.merge .popRight 1) inputs outputs =>
    .assume (inputs.length = 3 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let inputL := inputs[1]'(by omega)
    let inputR := inputs[2]'(by omega)
    let output := outputs[0]'(by omega)
    let val ← .checkFromConst decider
    if let some val := InterpConsts.toBool val then
      if val then
        -- The left input is never consumed
        return [
          .forward #v[inputR] #v[output],
          .sink #v[decider],
          .sink #v[inputL],
        ]
    failure
  -- TODO: these rewrites might be a bit risky and may change deadlock behavior
  | .async (.merge .decider 1) inputs outputs =>
    .assume (inputs.length = 3 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let inputL := inputs[1]'(by omega)
    let inputR := inputs[2]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseNames (inputs ++ outputs) λ
    -- Merge -> steer can be optimized to a steer and a sink
    -- if they have the same decider (both deciders coming from a fork)
    | .async (.steer flavor 1) inputs' outputs' =>
      .assume (inputs'.length = 2 ∧ outputs'.length = 1) λ h => do
      let decider' := inputs'[0]'(by omega)
      let input' := inputs'[1]'(by omega)
      let output' := outputs'[0]'(by omega)
      .assumeFromSameFork decider decider'
      if output = input' then
        if flavor then
          return [
            -- Pass RHS (true side) through and sink LHS (false side)
            .steer true decider #v[inputR] #v[output'],
            .sink #v[decider'],
            .sink #v[inputL],
          ]
        else
          return [
            -- Pass LHS (false side) through and sink RHS (true side)
            .steer false decider #v[inputL] #v[output'],
            .sink #v[decider'],
            .sink #v[inputR],
          ]
      else failure
    -- Merge in the decider state with a constant false LHS and constant true RHS
    -- can be rewritten to a forward from the decider
    | .async (.const v₁ 1) inputs₁ outputs₁ =>
      .chooseNames (inputs ++ outputs) λ
      | .async (.const v₂ 1) inputs₂ outputs₂ =>
        .assume (inputs₁.length = 1 ∧ outputs₁.length = 1 ∧
          inputs₂.length = 1 ∧ outputs₂.length = 1) λ h => do
        let outputs₁ := outputs₁[0]'(by omega)
        let outputs₂ := outputs₂[0]'(by omega)
        if inputL = outputs₁ ∧ inputR = outputs₂ ∧
          InterpConsts.toBool v₁ = some false ∧
          InterpConsts.toBool v₂ = some true then
          return [
            .forward #v[decider] #v[output],
            .sink #v[inputs₁[0]'(by omega)],
            .sink #v[inputs₂[0]'(by omega)],
          ]
        else failure
      | _ => failure
    | _ => failure
  | _ => failure

end Wavelet.Compile
