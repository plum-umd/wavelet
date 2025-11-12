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

/-- A successful rewrite would return a name for the rewrite rule applied,
and the rewritten atoms. -/
abbrev Rewrite Op χ V [Arity Op] [DecidableEq χ] [Hashable χ] :=
  RewriteM Op χ V (String × AtomicProcs Op (RewriteName χ) V)

/-- For debugging purposes. -/
def allRewriteNames : List String := [
    "n-ary-switch",
    "n-ary-merge",
    "n-ary-steer",
    "n-ary-const",
    "n-ary-forwardc",
    "n-ary-forward",
    "n-ary-sink",
    "inact-0",

    "fold-forward-aop-receiver",
    "fold-forward-aop-sender",
    "fold-forward-op-receiver",
    "fold-forward-op-sender",
    "switch-sink-left",
    "switch-sink-right",
    "steer-const-true",
    "steer-const-false",
    "steer-sink",
    "steer-steer",
    "steer-order-steer",
    "par-steer-steer",
    "steer-fork-steer",
    "const-steer",
    "fork-0",
    "fork-1",
    "fork-sink",
    "fork-fork",
    "order-1",
    "order-order",
    "order-sync-path",
    "order-sink",
    "order-const",
    "order-const-head",
    "const-sink",
    "inact-sink",
    "carry-fork-steer-to-inv-left",
    "carry-fork-steer-to-inv-right",
    "carry-steer-cycle-to-sink",
    "carry-order-steer-cycle-to-sink",
    "carry-false",
    "carry-true",
    "merge-sink",
    "merge-steer-true",
    "merge-steer-false",
    "merge-dedup",
    "merge-same-const",
    "merge-true-false-const",
  ]

def Rewrite.apply [Arity Op] [DecidableEq χ] [Hashable χ]
  (rw : Rewrite Op χ V)
  (proc : Proc Op (RewriteName χ) V m n) :
    Option (String × Proc Op (RewriteName χ) V m n) := do
  let ((rwName, aps'), s) ← rw.run (.init proc.atoms)
  let unmatched := s.aps.mapIdx (·, ·)
    |>.filter (λ (i, _) => i ∉ s.matched)
    |>.map (·.snd)
  -- Final renaming to avoid name conflicts in the future
  return (rwName, {
    inputs := proc.inputs.map .rw,
    outputs := proc.outputs.map .rw,
    atoms := AtomicProcs.mapChans .rw (aps' ++ unmatched)
  })

/-- Apply the given rewrite until failure. -/
partial def Rewrite.applyUntilFail
  [Arity Op] [DecidableEq χ] [Hashable χ]
  (rw : Rewrite Op χ V)
  (proc : Proc Op (RewriteName χ) V m n) : Nat × Proc Op (RewriteName χ) V m n :=
    loop 0 proc
  where
    loop numRewrites proc : Nat × Proc Op (RewriteName χ) V m n :=
      match rw.apply proc with
      | some (_rwName, proc') => loop (numRewrites + 1) proc'
      | none => (numRewrites, proc)

/-- Similar to `applyUntilFail` but performs `renameChans` every round
for slightly better performance, and also returns some stats about
rewrite rules used. -/
partial def Rewrite.applyUntilFailNat
  [Arity Op] [DecidableEq χ]
  (rw : Rewrite Op Nat V)
  (proc : Proc Op χ V m n) : Nat × Std.HashMap String Nat × Proc Op Nat V m n :=
    loop 0 proc.renameChans initStats
  where
    initStats := allRewriteNames.foldl (λ m name => m.insert name 0)
      (Std.HashMap.emptyWithCapacity allRewriteNames.length)
    loop numRewrites proc stats :=
      match rw.apply (proc.mapChans .base) with
      | some (rwName, proc') =>
        let stats := stats.insert rwName (stats.getD rwName 0 + 1)
        loop (numRewrites + 1) proc'.renameChans stats
      | none => (numRewrites, stats, proc.renameChans)

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
def RewriteM.chooseWithNames [Arity Op] [DecidableEq χ] [Hashable χ]
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
    -- |>.filter (λ (i, _) => i ∉ s.matched)
    |>.map (·.snd)

/-- Gets the list of operators that reference the give names in the context. -/
@[always_inline]
def RewriteM.ctxWithNames [Arity Op] [DecidableEq χ] [Hashable χ]
  (names : List (RewriteName χ)) :
    RewriteM Op χ V (AtomicProcs Op (RewriteName χ) V) := do
  let s ← get
  return names.map (s.chanToAtoms.getD · [])
    |>.flatten
    -- |>.filter (↑· ∉ s.matched)
    |>.map (s.aps[·])

/-- Similar to `ctxWithNames` but keeps atom indices. -/
@[always_inline]
def RewriteM.idxCtxWithNames [Arity Op] [DecidableEq χ] [Hashable χ]
  (names : List (RewriteName χ)) :
    RewriteM Op χ V (List (Nat × AtomicProc Op (RewriteName χ) V)) := do
  let s ← get
  return names.map (s.chanToAtoms.getD · [])
    |>.flatten
    -- |>.filter (↑· ∉ s.matched)
    |>.map (λ i : Fin _ => (↑i, s.aps[i]))

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

/-- Checks if the given name has a "synchronous path"
to the other set of output names, where a synchronous path
means a path going through only synchronous operators, forks,
orders, consts. -/
partial def RewriteM.checkSyncPathTo
  [Arity Op] [DecidableEq χ] [Hashable χ]
  (chan : RewriteName χ)
  (outputs : List (RewriteName χ))
  (hist : List Nat := []) :
    RewriteM Op χ V Unit
  := do
  if chan ∈ outputs then
    return ()
  else
    (← .idxCtxWithNames [chan]).firstM λ (i, ap) =>
    if i ∈ hist then
      failure -- Avoid cycles
    else
      match ap with
      | .op _ inputs' outputs' =>
        if chan ∈ outputs' then
          inputs'.firstM λ input' =>
            RewriteM.checkSyncPathTo input' outputs (i :: hist)
        else failure
      | .async (AsyncOp.fork _) inputs' outputs'
      | .async (AsyncOp.order _) inputs' outputs'
      | .async (AsyncOp.const _ _) inputs' outputs' =>
        if chan ∈ outputs' then
          inputs'.firstM λ input' =>
            RewriteM.checkSyncPathTo input' outputs (i :: hist)
        else failure
      | _ => failure

/-- Lowers n-ary async operators to unary operators. -/
def naryLowering
  [Arity Op] [DecidableEq χ] [Hashable χ] :
    Rewrite Op χ V :=
  .choose λ
  | .async (AsyncOp.switch k) (decider :: inputs) outputs =>
    .assume (k > 1) λ h => do
    let deciders := (Vector.finRange k).map (.rename · decider)
    let inputs ← inputs.toVectorDyn k
    let outputs₁ ← (outputs.take k).toVectorDyn k
    let outputs₂ ← (outputs.drop k).toVectorDyn k
    return .mk "n-ary-switch" <| .fork decider deciders ::
      (deciders ⊗ inputs ⊗ outputs₁ ⊗ outputs₂ |>.map
        λ ⟨d, i, o₁, o₂⟩ => .switch d #v[i] #v[o₁] #v[o₂]).toList
  | .async (AsyncOp.merge st k) (decider :: inputs) outputs =>
    .assume (k > 1) λ h => do
    let deciders := (Vector.finRange k).map (.rename · decider)
    let inputs₁ ← (inputs.take k).toVectorDyn k
    let inputs₂ ← (inputs.drop k).toVectorDyn k
    let outputs ← outputs.toVectorDyn k
    return .mk "n-ary-merge" <| .fork decider deciders ::
      (deciders ⊗ inputs₁ ⊗ inputs₂ ⊗ outputs |>.map
        λ ⟨d, i₁, i₂, o⟩ => .carry st d #v[i₁] #v[i₂] #v[o]).toList
  | .async (AsyncOp.steer flavor k) (decider :: inputs) outputs =>
    .assume (k > 1) λ h => do
    let deciders := (Vector.finRange k).map (.rename · decider)
    let inputs ← inputs.toVectorDyn k
    let outputs ← outputs.toVectorDyn k
    return .mk "n-ary-steer" <| .fork decider deciders ::
      (deciders ⊗ inputs ⊗ outputs |>.map
        λ ⟨d, i, o⟩ => .steer flavor d #v[i] #v[o]).toList
  -- Rewrite `const v k` with a fork and `k` unary `const`s
  | .async (AsyncOp.const v k) inputs outputs =>
    .assume (k > 1 ∧ inputs.length = 1 ∧ outputs.length = k) λ h => do
    let act := inputs[0]'(by omega)
    -- Copy activation signals
    let acts := (Vector.finRange k).map (.rename · act)
    let outputs : Vector _ k := outputs.toVector.cast (by omega)
    return .mk "n-ary-const" <| .fork act acts ::
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
    return .mk "n-ary-forwardc" (
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
    return .mk "n-ary-forward"
      (inputs ⊗ outputs |>.map λ ⟨i, o⟩ => .forward #v[i] #v[o]).toList
  | .async (AsyncOp.sink n) inputs outputs =>
    .assume (n > 1 ∧ inputs.length = n ∧ outputs.length = 0) λ h => do
    let inputs : Vector _ n := inputs.toVector.cast (by omega)
    return .mk "n-ary-sink" (inputs.map λ i => .sink #v[i]).toList
  | .async (.inact 0) _ _ => return .mk "inact-0" []
  | _ => failure

/-- Optimizing combinations of various operators. -/
def deadCodeElim
  [Arity Op] [DecidableEq χ] [Hashable χ]
  [InterpConsts V] [DecidableEq V] :
    Rewrite Op χ V :=
  .choose λ
  -- Two orders coming into a synchronized operator can be combined
  | .op _ inputs outputs =>
    .chooseWithNames (inputs.toList ++ outputs.toList) λ
    | .async (AsyncOp.order n) inputs₁ outputs₁ =>
      .assume (n > 0 ∧ inputs₁.length = n ∧ outputs₁.length = 1) λ h => do
      let input₁ := inputs₁[0]'(by omega)
      let output₁ := outputs₁[0]'(by omega)
      if output₁ ∈ inputs then
        .chooseWithNames (inputs.toList ++ outputs.toList) λ
        | .async (AsyncOp.order m) inputs₂ outputs₂ =>
          .assume (m > 0 ∧ inputs₂.length = m ∧ outputs₂.length = 1) λ h => do
          let output₂ := outputs₂[0]'(by omega)
          if output₂ ∈ inputs then
            let : NeZero (inputs₁.tail ++ inputs₂).length := by
              constructor
              simp
              intros h₃ h₄
              subst h₄
              simp at h
              omega
            return .mk "sync-order-order" [
              .op _ (inputs.replace output₁ input₁) outputs,
              .order (inputs₁.tail ++ inputs₂).toVector output₂,
            ]
          else failure
        | _ => failure
      else failure
    | _ => failure
  -- Forwards can be folded into either the sender or the receiver
  -- depending on which is available.
  | .async (.forward 1) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    let input := inputs[0]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseWithNames [input, output] λ
    | .async aop inputs' outputs' => do
      if output ∈ inputs' then
        return .mk "fold-forward-aop-receiver" [.async aop (inputs'.replace output input) outputs']
      else if input ∈ outputs' then
        return .mk "fold-forward-aop-sender" [.async aop inputs' (outputs'.replace input output)]
      else failure
    | .op op inputs' outputs' => do
      if output ∈ inputs' then
        return .mk "fold-forward-op-receiver" [.op op (inputs'.replace output input) outputs']
      else if input ∈ outputs' then
        return .mk "fold-forward-op-sender" [.op op inputs' (outputs'.replace input output)]
      else failure
  | .async (.switch 1) inputs outputs =>
    .assume (inputs.length = 2 ∧ outputs.length = 2) λ h => do
    let decider := inputs[0]'(by omega)
    let input := inputs[1]'(by omega)
    let output₁ := outputs[0]'(by omega)
    let output₂ := outputs[1]'(by omega)
    .chooseWithNames [output₁, output₂] λ
    -- Switch with one of the outputs being a sink can be reduced to a steer
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if output₁ = sink then
        return .mk "switch-sink-left" [.steer false decider #v[input] #v[output₂]]
      else if output₂ = sink then
        return .mk "switch-sink-right" [.steer true decider #v[input] #v[output₁]]
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
          return .mk "steer-const-true" [.order #v[input, decider] output]
        else
          return .mk "steer-const-false" [
            .sink #v[input],
            .sink #v[decider],
            .inact #v[output],
          ]
      failure) <|>
    .chooseWithNames (inputs ++ outputs) λ
    -- Steer with a sink output can be reduced to two sinks on the decider and the input
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if output = sink then
        return .mk "steer-sink" [
          .sink #v[input],
          .sink #v[decider],
        ]
      else failure
    | .async (.steer flavor' 1) inputs' outputs' =>
      .assume (inputs'.length = 2 ∧ outputs'.length = 1) λ h => do
      let decider' := inputs'[0]'(by omega)
      let input' := inputs'[1]'(by omega)
      let output' := outputs'[0]'(by omega)
      .assumeFromSameFork decider decider'
      if flavor = flavor' ∧ output = input' then
        -- Two consecutive steers with the same flavor and same decider can be folded
        return .mk "steer-steer" [
          .steer flavor decider #v[input] #v[output'],
          .sink #v[decider'],
        ]
      else
        failure
    -- A specific pattern of `steer → order → steer`
    -- can be reduced to `steer → order` if the deciders and flavors match
    | .async (AsyncOp.order n) inputs' outputs' =>
      .assume (n > 0 ∧ inputs'.length = n ∧ outputs'.length = 1) λ h => do
      let output' := outputs'[0]'(by omega)
      let inputs' ← inputs'.toVectorDyn n
      if output ∈ inputs' then -- The steer output doesn't have to be the first order input
        .chooseWithNames [output'] λ
        | .async (.steer flavor'' 1) inputs'' outputs'' => do
          .assume (inputs''.length = 2 ∧ outputs''.length = 1) λ h => do
          let decider'' := inputs''[0]'(by omega)
          let input'' := inputs''[1]'(by omega)
          let output'' := outputs''[0]'(by omega)
          if flavor = flavor'' ∧ output' = input'' then
            .assumeFromSameFork decider decider''
            return .mk "steer-order-steer" [
              .steer flavor decider #v[input] #v[output], -- Same steer
              .order inputs' output'', -- order directly send to second steer output
              .sink #v[decider''],
            ]
          else failure
        | _ => failure
      else failure
    | .async (.fork n) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = n) λ h => do
      let input' := inputs'[0]'(by omega)
      let outputs' ← outputs'.toVectorDyn n
      .chooseWithNames outputs'.toList λ
      | .async (.steer flavor'' 1) inputs'' outputs'' =>
        .assume (inputs''.length = 2 ∧ outputs''.length = 1) λ h => do
        let decider'' := inputs''[0]'(by omega)
        let input'' := inputs''[1]'(by omega)
        let output'' := outputs''[0]'(by omega)
        if flavor = flavor'' then
          .assumeFromSameFork decider decider''
          -- Two parallel steers with the same flavor and same input can be combined
          (do
            .assumeFromSameFork input input''
            return .mk "par-steer-steer" [
              .fork input' outputs',
              .steer flavor decider #v[input] #v[.rename 0 output],
              .sink #v[decider''],
              .sink #v[input''],
              .fork (.rename 0 output) #v[output, output''],
            ]) <|>
          -- Two consecutive steers (gated by a fork) with the same flavor can be folded
          (do
            if input'' ∈ outputs' ∧ input' ∈ outputs then
              return .mk "steer-fork-steer" [
                .fork input' (outputs'.push output''), -- Add one more result to fork
                .sink #v[decider''], -- Following steer removed
                .sink #v[input''],
                .steer flavor decider #v[input] #v[output], -- Original steer kept the same
              ]
            else failure)
        else failure
      | _ => failure
    -- Const followed by a steer can commute (this can move const closer to sync
    -- operators and expose more optimization opportunities)
    | .async (.const v 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 1) λ h => do
      let act := inputs'[0]'(by omega)
      let output' := outputs'[0]'(by omega)
      if output' = input then
        return .mk "const-steer" [
          .steer flavor decider #v[act] #v[output'],
          .const v output' #v[output],
        ]
      else failure
    | _ => failure
  -- Fork with zero outputs can be replaced with a sink (which enables further rewrites)
  | .async (.fork 0) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = 0) λ h => do
    return .mk "fork-0" [.sink inputs.toVector]
  -- Fork with exactly one output is a forward
  | .async (.fork 1) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    return .mk "fork-1" [.forward #v[inputs[0]] #v[outputs[0]]]
  -- Fork with one of the outputs being a sink or another fork
  | .async (.fork n) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = n) λ h => do
    let input := inputs[0]'(by omega)
    .chooseWithNames (inputs ++ outputs) λ
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if sink ∈ outputs then
        return .mk "fork-sink" [.fork input (outputs.erase sink).toVector]
      else failure
    -- Folding two consecutive forks
    | .async (.fork m) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = m) λ h => do
      let input' := inputs'[0]'(by omega)
      if input' ∈ outputs then
        return .mk "fork-fork" [.fork input (outputs.erase input' ++ outputs').toVector]
      else failure
    | _ => failure
  -- Order with one input can be rewritten to a forward
  | .async (.order 1) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    let input := inputs[0]'(by omega)
    let output := outputs[0]'(by omega)
    return .mk "order-1" [.forward #v[input] #v[output]]
  | .async (AsyncOp.order n) inputs outputs =>
    .assume (n > 1 ∧ inputs.length = n ∧ outputs.length = 1) λ h => do
    let output := outputs[0]'(by omega)
    .chooseWithNames (inputs ++ outputs) λ
    -- Nested order can be folded
    | .async (AsyncOp.order m) inputs' outputs' =>
      .assume (m > 1 ∧ inputs'.length = m ∧ outputs'.length = 1) λ h => do
      let output' := outputs'[0]'(by omega)
      if output ∈ inputs' then
        let newInputs' := inputs'
          |>.map (λ name => if name = output then inputs else [name])
          |>.flatten
        .assume (newInputs'.length ≠ 0) λ h' => do
        let : NeZero newInputs'.length := by constructor; omega
        return .mk "order-order" [
          .order newInputs'.toVector output',
        ]
      else
        failure
    -- If an order has two inputs, one (non-first) input from
    -- a fork and another one tracing back to the same fork through
    -- a "synchronous path", then that non-first input can be removed.
    | .async (.fork m) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = m) λ h =>
      let input' := inputs'[0]'(by omega)
      (inputs.drop 1).firstM λ input₁ =>
        if input₁ ∈ outputs' then
          inputs.firstM λ input₂ => do
            if input₁ ≠ input₂ then
              .checkSyncPathTo input₂ outputs'
              let newInputs := inputs.erase input₁
              let newOutputs' := outputs'.erase input₁
              .assume (newInputs.length ≠ 0) λ h' => do
              let : NeZero newInputs.length := by constructor; omega
              return .mk "order-sync-path" [
                .fork input' newOutputs'.toVector,
                .order newInputs.toVector output,
              ]
            else failure
        else failure
    -- Order -> sink can be optimized away
    | .async (AsyncOp.sink n) inputs' outputs' =>
      .assume (n > 0 ∧ inputs'.length = n ∧ outputs'.length = 0) λ h => do
      if output ∈ inputs' then
        return .mk "order-sink" [
          .sink inputs.toVector,
          .sink (inputs'.erase output).toVector,
        ]
      else failure
    -- Waiting on a constant is the same as waiting for its activation signal
    | .async (.const v 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 1) λ h => do
      let act := inputs'[0]'(by omega)
      let output' := outputs'[0]'(by omega)
      if output' ∈ inputs ∧ output' ≠ inputs[0] then
        let : NeZero (inputs.erase output' ++ [act]).length := by constructor; simp
        return .mk "order-const" [
          .order (inputs.erase output' ++ [act]).toVector output,
        ]
      else if output' = inputs[0] then
        let : NeZero (act :: inputs.tail).length := by constructor; simp
        return .mk "order-const-head" [
          .order (act :: inputs.tail).toVector output',
          .const v output' #v[output],
        ]
      else failure
    -- If an order has two inputs that come from two steers
    -- of the same flavor and decider, then we can pop the order
    -- up to synchronize the inputs to the two steers instead.
    | .async (AsyncOp.steer flavor 1) inputs₁ outputs₁ =>
      .assume (n = 2) λ h₁ => do
      let orderInput₁ := inputs[0]'(by omega)
      let orderInput₂ := inputs[1]'(by omega)
      .assume (inputs₁.length = 2 ∧ outputs₁.length = 1) λ h₂ => do
      let decider₁ := inputs₁[0]'(by omega)
      let input₁ := inputs₁[1]'(by omega)
      let output₁ := outputs₁[0]'(by omega)
      .chooseWithNames (inputs ++ outputs) λ
      | .async (AsyncOp.steer flavor' 1) inputs₂ outputs₂ =>
        .assume (inputs₂.length = 2 ∧ outputs₂.length = 1) λ h₃ => do
        let decider₂ := inputs₂[0]'(by omega)
        let input₂ := inputs₂[1]'(by omega)
        let output₂ := outputs₂[0]'(by omega)
        .assumeFromSameFork decider₁ decider₂
        if flavor = flavor' ∧ output₁ = orderInput₁ ∧ output₂ = orderInput₂ then
          return .mk "order-steer-steer" [
            .order #v[input₁, input₂] output₁,
            .steer flavor decider₁ #v[output₁] #v[output],
            .sink #v[decider₂],
          ]
        else failure
      | _ => failure
    | _ => failure
  -- Constant with a sink output can be rewritten to a sink
  | .async (.const v 1) inputs outputs =>
    .assume (inputs.length = 1 ∧ outputs.length = 1) λ h => do
    let act := inputs[0]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseWithNames (inputs ++ outputs) λ
    | .async (.sink 1) inputs' outputs' =>
      .assume (inputs'.length = 1 ∧ outputs'.length = 0) λ h => do
      let sink := inputs'[0]'(by omega)
      if output = sink then
        return .mk "const-sink" [.sink #v[act]]
      else failure
    | _ => failure
  | .async (.inact n) inputs outputs =>
    .assume (n > 0 ∧ inputs.length = 0 ∧ outputs.length = n) λ h => do
    .chooseWithNames outputs λ
    -- Inact + sink : the channel between them can be removed
    | .async (AsyncOp.sink m) inputs' outputs' =>
      .assume (inputs'.length = m ∧ outputs'.length = 0) λ h => do
      if ¬ outputs.Disjoint inputs' then
        return .mk "inact-sink" [
          .inact (outputs.removeAll inputs').toVector,
          .sink (inputs'.removeAll outputs).toVector,
        ]
      else failure
    | _ => failure
  -- Carry (true flavor)
  | .async (.merge .popLeft 1) inputs outputs =>
    .assume (inputs.length = 3 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let inputL := inputs[1]'(by omega)
    let inputR := inputs[2]'(by omega)
    let output := outputs[0]'(by omega)
    (do
      .chooseWithNames outputs λ
      -- If we have:
      --   |
      -- carry -> fork 2 -> other output
      --           |
      --         steer -> (back to carry)
      -- such that carry and steer share the same decider
      -- Then this can be rewritten to an invariant operator (true flavor)
      --
      -- Note that this only addresses recursion constants
      -- that are used at the top level of a function, without
      -- going through any branches.
      | .async (.fork 2) inputs' outputs' =>
        .assume (inputs'.length = 1 ∧ outputs'.length = 2) λ h =>
        let input' := inputs'[0]'(by omega)
        let output₁' := outputs'[0]'(by omega)
        let output₂' := outputs'[1]'(by omega)
        if output = input' then
          .chooseWithNames outputs' λ
          | .async (.steer true 1) inputs'' outputs'' =>
            .assume (inputs''.length = 2 ∧ outputs''.length = 1) λ h => do
            let decider'' := inputs''[0]'(by omega)
            let input'' := inputs''[1]'(by omega)
            let output'' := outputs''[0]'(by omega)
            .assumeFromSameFork decider decider''
            if output'' = inputR then
              if input'' = output₁' then
                return .mk "carry-fork-steer-to-inv-left" [
                  .inv true none decider inputL output₂',
                  .sink #v[decider''],
                ]
              else if input'' = output₂' then
                return .mk "carry-fork-steer-to-inv-right" [
                  .inv true none decider inputL output₁',
                  .sink #v[decider''],
                ]
              else failure
            else failure
          | _ => failure
        else failure
      | .async (.steer true 1) inputs' outputs' =>
        .assume (inputs'.length = 2 ∧ outputs'.length = 1) λ h => do
        let decider' := inputs'[0]'(by omega)
        let input' := inputs'[1]'(by omega)
        let output' := outputs'[0]'(by omega)
        .assumeFromSameFork decider decider'
        if output = input' ∧ output' = inputR then
          -- If we have:
          --   |
          -- carry -> steer -> (back to carry)
          -- such that carry and steer share the same decider
          -- Then this is essentially a sink (assuming no deadlocks in the original program)
          return .mk "carry-steer-cycle-to-sink" [.sink #v[decider, decider', inputL]]
        else
          -- Similar to the case above, if we have:
          --   |
          -- carry -> order -> steer -> (back to carry)
          -- such that carry and steer share the same decider
          -- Then this is essentially a sink (assuming no deadlocks in the original program)
          .chooseWithNames [output'] λ
          | .async (AsyncOp.order n) inputs'' outputs'' =>
            .assume (n > 0 ∧ inputs''.length = n ∧ outputs''.length = 1) λ h => do
            let output'' := outputs''[0]'(by omega)
            if output = input' ∧ output' ∈ inputs'' ∧ output'' = inputR then
              return .mk "carry-order-steer-cycle-to-sink" [
                .sink (#v[
                  decider, decider', inputL,
                ] ++ (inputs''.erase output').toVector)
              ]
            else failure
          | _ => failure
      | _ => failure) <|>
    -- Carry (true flavor) with a constant false decider
    (do
      let val ← .checkFromConst decider
      if let some val := InterpConsts.toBool val then
        if ¬val then
          -- The right input is never consumed
          return .mk "carry-false" [
            .forward #v[inputL] #v[output],
            .sink #v[decider],
            .sink #v[inputR],
          ]
      failure)
  -- Carry (false flavor) with a constant true decider
  | .async (.merge .popRight 1) inputs outputs =>
    .assume (inputs.length = 3 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let inputL := inputs[1]'(by omega)
    let inputR := inputs[2]'(by omega)
    let output := outputs[0]'(by omega)
    -- TODO: add the false flavor version of the invariant rewrite above
    let val ← .checkFromConst decider
    if let some val := InterpConsts.toBool val then
      if val then
        -- The left input is never consumed
        return .mk "carry-true" [
          .forward #v[inputR] #v[output],
          .sink #v[decider],
          .sink #v[inputL],
        ]
    failure
  | .async (.merge .decider 1) inputs outputs =>
    .assume (inputs.length = 3 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let inputL := inputs[1]'(by omega)
    let inputR := inputs[2]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseWithNames (inputs ++ outputs) λ
    -- Merge -> sink can be optimized away
    | .async (AsyncOp.sink n) inputs' outputs' =>
      .assume (n > 0 ∧ inputs'.length = n ∧ outputs'.length = 0) λ h => do
      if output ∈ inputs' then
        return .mk "merge-sink" [
          .sink #v[decider],
          .sink #v[inputL],
          .sink #v[inputR],
          .sink (inputs'.erase output).toVector,
        ]
      else failure
    -- Merge -> steer can be optimized to a forward and a sink
    -- if they have the same decider (both deciders coming from a fork)
    | .async (.steer flavor 1) inputs' outputs' =>
      .assume (inputs'.length = 2 ∧ outputs'.length = 1) λ h => do
      let decider' := inputs'[0]'(by omega)
      let input' := inputs'[1]'(by omega)
      let output' := outputs'[0]'(by omega)
      .assumeFromSameFork decider decider'
      if output = input' then
        if flavor then
          return .mk "merge-steer-true" [
            -- Pass RHS (true side) through and sink LHS (false side)
            .forward #v[inputR] #v[output'],
            .sink #v[decider, decider', inputL],
          ]
        else
          return .mk "merge-steer-false" [
            -- Pass LHS (false side) through and sink RHS (true side)
            .forward #v[inputL] #v[output'],
            .sink #v[decider, decider', inputR],
          ]
      else failure
    -- Two merges with the same left/right/decider channels from the same fork
    -- can be merged. TODO: make this a more general dedup rewrite rule.
    | .async (.fork n) inputs₀ outputs₀ =>
      -- Finding an intermediate fork first to make this more efficient
      -- (without quadratic cost)
      .chooseWithNames (inputs₀ ++ outputs₀) λ
      | .async (.merge .decider 1) inputs' outputs' =>
        .assume (inputs'.length = 3 ∧ outputs'.length = 1) λ h => do
        let decider' := inputs'[0]'(by omega)
        let inputL' := inputs'[1]'(by omega)
        let inputR' := inputs'[2]'(by omega)
        let output' := outputs'[0]'(by omega)
        .assumeFromSameFork decider decider'
        .assumeFromSameFork inputL inputL'
        .assumeFromSameFork inputR inputR'
        return .mk "merge-dedup" [
          .async (.fork n) inputs₀ outputs₀,
          .merge decider #v[inputL] #v[inputR] #v[.rename 0 output],
          .fork (.rename 0 output) #v[output, output'],
          .sink #v[decider', inputL', inputR'],
        ]
      | _ => failure
    -- Merging constants
    | .async (.const v₁ 1) inputs₁ outputs₁ =>
      .assume (inputs₁.length = 1 ∧ outputs₁.length = 1) λ h => do
      let input₁ := inputs₁[0]'(by omega)
      let outputs₁ := outputs₁[0]'(by omega)
      .chooseWithNames (inputs ++ outputs) λ
      | .async (.const v₂ 1) inputs₂ outputs₂ =>
        .assume (inputs₂.length = 1 ∧ outputs₂.length = 1) λ h => do
        let input₂ := inputs₂[0]'(by omega)
        let outputs₂ := outputs₂[0]'(by omega)
        if inputL = outputs₁ ∧ inputR = outputs₂ then
          if v₁ = v₂ then
            -- Merging the same constant: push the constant to merge output
            return .mk "merge-same-const" [
              .merge decider #v[input₁] #v[input₂] #v[.rename 0 output],
              .const v₁ (.rename 0 output) #v[output],
            ]
          else  if InterpConsts.toBool v₁ = some false ∧
            InterpConsts.toBool v₂ = some true then
            return .mk "merge-true-false-const" [
              .forward #v[decider] #v[output],
              .sink #v[inputs₁[0]'(by omega)],
              .sink #v[inputs₂[0]'(by omega)],
            ]
          else failure
        else failure
      | _ => failure
    | _ => failure
  | _ => failure

end Wavelet.Compile
