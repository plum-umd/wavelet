import Wavelet.Compile.Rewrite

/-!
A declarative description of the successful runs of `deadCodeElim`:
`DCEMatch aps matched name res` says that rule `name` matched the atoms
of `aps` at indices `matched` (in the order of `RewriteState.matched`,
i.e., the last matched atom first) and produced the atoms `res`.
-/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

/-- `chan` only carries copies of `v` (from a constant, possibly through a fork),
as checked by `RewriteM.checkFromConst`. -/
inductive FromConst [Arity Op] (aps : AtomicProcs Op χ V) (chan : χ) (v : V) : Prop
  | const :
    .async (.const v k) ins outs ∈ aps → chan ∈ outs → FromConst aps chan v
  | fork :
    .async (.fork k) [x] outs ∈ aps → chan ∈ outs →
    .async (.const v k') ins' outs' ∈ aps → x ∈ outs' →
    FromConst aps chan v

/-- Two channels are outputs of the same fork, as checked by `RewriteM.assumeFromSameFork`. -/
def SameFork [Arity Op] (aps : AtomicProcs Op χ V) (chan₁ chan₂ : χ) : Prop :=
  ∃ k ins outs, .async (.fork k) ins outs ∈ aps ∧ chan₁ ∈ outs ∧ chan₂ ∈ outs

/-- Rules of `deadCodeElim` that are not forward simulations in general. -/
def excludedRules : List String := ["steer-steer", "steer-order-steer", "steer-fork-steer"]

inductive DCEMatch [Arity Op] [DecidableEq χ] [InterpConsts V]
  (aps : AtomicProcs Op (RewriteName χ) V) :
    List Nat → String → AtomicProcs Op (RewriteName χ) V → Prop
  | sync_order_order
    {o : Op} {inputs : Vector (RewriteName χ) (Arity.ι o)} {outputs : Vector (RewriteName χ) (Arity.ω o)}
    {n k : Nat} [NeZero n] [NeZero k]
    {input₁ output₁ output₂ : RewriteName χ} {rest₁ inputs₂ : List (RewriteName χ)}
    [NeZero (inputs₂ ++ rest₁).length]
    (h₁ : aps[i₁]? = some (.op o inputs outputs))
    (h₂ : aps[i₂]? = some (.async (.order n) (input₁ :: rest₁) [output₁]))
    (h₃ : aps[i₃]? = some (.async (.order k) inputs₂ [output₂]))
    (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
    (hlen₁ : (input₁ :: rest₁).length = n) (hlen₂ : inputs₂.length = k)
    (hmem₁ : output₁ ∈ inputs) (hmem₂ : output₂ ∈ inputs) :
    DCEMatch aps [i₃, i₂, i₁] "sync-order-order" [
      .op o (inputs.replace output₁ input₁) outputs,
      .order (inputs₂ ++ rest₁).toVector output₂,
    ]
  | fold_forward_aop_receiver
    {input output : RewriteName χ} {aop : AsyncOp V} {inputs' outputs' : List (RewriteName χ)}
    (h₁ : aps[i₁]? = some (.async (.forward 1) [input] [output]))
    (h₂ : aps[i₂]? = some (.async aop inputs' outputs'))
    (hne : i₂ ≠ i₁)
    (hmem : output ∈ inputs') :
    DCEMatch aps [i₂, i₁] "fold-forward-aop-receiver"
      [.async aop (inputs'.replace output input) outputs']
  | fold_forward_aop_sender
    {input output : RewriteName χ} {aop : AsyncOp V} {inputs' outputs' : List (RewriteName χ)}
    (h₁ : aps[i₁]? = some (.async (.forward 1) [input] [output]))
    (h₂ : aps[i₂]? = some (.async aop inputs' outputs'))
    (hne : i₂ ≠ i₁)
    (hnmem : output ∉ inputs')
    (hmem : input ∈ outputs') :
    DCEMatch aps [i₂, i₁] "fold-forward-aop-sender"
      [.async aop inputs' (outputs'.replace input output)]
  | fold_forward_op_receiver
    {input output : RewriteName χ} {o : Op} {inputs' : Vector (RewriteName χ) (Arity.ι o)} {outputs' : Vector (RewriteName χ) (Arity.ω o)}
    (h₁ : aps[i₁]? = some (.async (.forward 1) [input] [output]))
    (h₂ : aps[i₂]? = some (.op o inputs' outputs'))
    (hne : i₂ ≠ i₁)
    (hmem : output ∈ inputs') :
    DCEMatch aps [i₂, i₁] "fold-forward-op-receiver"
      [.op o (inputs'.replace output input) outputs']
  | fold_forward_op_sender
    {input output : RewriteName χ} {o : Op} {inputs' : Vector (RewriteName χ) (Arity.ι o)} {outputs' : Vector (RewriteName χ) (Arity.ω o)}
    (h₁ : aps[i₁]? = some (.async (.forward 1) [input] [output]))
    (h₂ : aps[i₂]? = some (.op o inputs' outputs'))
    (hne : i₂ ≠ i₁)
    (hnmem : output ∉ inputs')
    (hmem : input ∈ outputs') :
    DCEMatch aps [i₂, i₁] "fold-forward-op-sender"
      [.op o inputs' (outputs'.replace input output)]
  | switch_sink_left
    {decider input output₁ output₂ : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.switch 1) [decider, input] [output₁, output₂]))
    (h₂ : aps[i₂]? = some (.async (.sink 1) [output₁] []))
    (hne : i₂ ≠ i₁) :
    DCEMatch aps [i₂, i₁] "switch-sink-left" [.steer false decider #v[input] #v[output₂]]
  | switch_sink_right
    {decider input output₁ output₂ : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.switch 1) [decider, input] [output₁, output₂]))
    (h₂ : aps[i₂]? = some (.async (.sink 1) [output₂] []))
    (hne : i₂ ≠ i₁)
    (hne' : output₁ ≠ output₂) :
    DCEMatch aps [i₂, i₁] "switch-sink-right" [.steer true decider #v[input] #v[output₁]]
  | steer_const_true
    {flavor : Bool} {decider input output : RewriteName χ} {v : V}
    (h₁ : aps[i₁]? = some (.async (.steer flavor 1) [decider, input] [output]))
    (hconst : FromConst aps decider v)
    (hbool : InterpConsts.toBool v = some flavor) :
    DCEMatch aps [i₁] "steer-const-true" [.order #v[input, decider] output]
  | steer_const_false
    {flavor b : Bool} {decider input output : RewriteName χ} {v : V}
    (h₁ : aps[i₁]? = some (.async (.steer flavor 1) [decider, input] [output]))
    (hconst : FromConst aps decider v)
    (hbool : InterpConsts.toBool v = some b)
    (hne : b ≠ flavor) :
    DCEMatch aps [i₁] "steer-const-false" [
      .sink #v[input],
      .sink #v[decider],
      .inact #v[output],
    ]
  | steer_sink
    {flavor : Bool} {decider input output : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.steer flavor 1) [decider, input] [output]))
    (h₂ : aps[i₂]? = some (.async (.sink 1) [output] []))
    (hne : i₂ ≠ i₁) :
    DCEMatch aps [i₂, i₁] "steer-sink" [.sink #v[input], .sink #v[decider]]
  | par_steer_steer
    {flavor : Bool} {decider input output input' decider'' input'' output'' : RewriteName χ}
    {k : Nat} {outputs' : List (RewriteName χ)}
    (h₁ : aps[i₁]? = some (.async (.steer flavor 1) [decider, input] [output]))
    (h₂ : aps[i₂]? = some (.async (.fork k) [input'] outputs'))
    (h₃ : aps[i₃]? = some (.async (.steer flavor 1) [decider'', input''] [output'']))
    (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
    (hlen : outputs'.length = k)
    (hfork₁ : SameFork aps decider decider'')
    (hfork₂ : SameFork aps input input'') :
    DCEMatch aps [i₃, i₂, i₁] "par-steer-steer" [
      .async (.fork k) [input'] outputs',
      .steer flavor decider #v[input] #v[.rename 0 output],
      .sink #v[decider''],
      .sink #v[input''],
      .fork (.rename 0 output) #v[output, output''],
    ]
  | const_steer
    {flavor : Bool} {decider input output act : RewriteName χ} {v : V}
    (h₁ : aps[i₁]? = some (.async (.steer flavor 1) [decider, input] [output]))
    (h₂ : aps[i₂]? = some (.async (.const v 1) [act] [input]))
    (hne : i₂ ≠ i₁) :
    DCEMatch aps [i₂, i₁] "const-steer" [
      .steer flavor decider #v[act] #v[.rename 0 act],
      .const v (.rename 0 act) #v[output],
    ]
  | fork_0
    {input : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.fork 0) [input] [])) :
    DCEMatch aps [i₁] "fork-0" [.sink [input].toVector]
  | fork_1
    {input output : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.fork 1) [input] [output])) :
    DCEMatch aps [i₁] "fork-1" [.forward #v[input] #v[output]]
  | fork_sink
    {k : Nat} {input sink : RewriteName χ} {outputs : List (RewriteName χ)}
    (h₁ : aps[i₁]? = some (.async (.fork k) [input] outputs))
    (h₂ : aps[i₂]? = some (.async (.sink 1) [sink] []))
    (hne : i₂ ≠ i₁)
    (hlen : outputs.length = k)
    (hmem : sink ∈ outputs) :
    DCEMatch aps [i₂, i₁] "fork-sink" [.fork input (outputs.erase sink).toVector]
  | fork_fork
    {k k' : Nat} {input input' : RewriteName χ} {outputs outputs' : List (RewriteName χ)}
    (h₁ : aps[i₁]? = some (.async (.fork k) [input] outputs))
    (h₂ : aps[i₂]? = some (.async (.fork k') [input'] outputs'))
    (hne : i₂ ≠ i₁)
    (hlen : outputs.length = k) (hlen' : outputs'.length = k')
    (hmem : input' ∈ outputs) :
    DCEMatch aps [i₂, i₁] "fork-fork" [.fork input (outputs.erase input' ++ outputs').toVector]
  | order_1
    {input output : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.order 1) [input] [output])) :
    DCEMatch aps [i₁] "order-1" [.forward #v[input] #v[output]]
  | order_order
    {n k : Nat} [NeZero n] [NeZero k] {inputs inputs' newInputs' : List (RewriteName χ)} {output output' : RewriteName χ}
    [NeZero newInputs'.length]
    (h₁ : aps[i₁]? = some (.async (.order n) inputs [output]))
    (h₂ : aps[i₂]? = some (.async (.order k) inputs' [output']))
    (hne : i₂ ≠ i₁)
    (hn : n > 1) (hlen : inputs.length = n)
    (hk : k > 1) (hlen' : inputs'.length = k)
    (hmem : output ∈ inputs')
    (hnew : newInputs' = (inputs'.map (λ name => if name = output then inputs else [name])).flatten) :
    DCEMatch aps [i₂, i₁] "order-order" [.order newInputs'.toVector output']
  | order_sync_path
    {n k : Nat} [NeZero n] {inputs outputs' : List (RewriteName χ)} {output input' input₁ : RewriteName χ}
    [NeZero (inputs.erase input₁).length]
    (h₁ : aps[i₁]? = some (.async (.order n) inputs [output]))
    (h₂ : aps[i₂]? = some (.async (.fork k) [input'] outputs'))
    (hne : i₂ ≠ i₁)
    (hn : n > 1) (hlen : inputs.length = n) (hlen' : outputs'.length = k)
    (hmem₁ : input₁ ∈ inputs.drop 1)
    (hmem₂ : input₁ ∈ outputs') :
    DCEMatch aps [i₂, i₁] "order-sync-path" [
      .fork input' (outputs'.erase input₁).toVector,
      .order (inputs.erase input₁).toVector output,
    ]
  | order_sink
    {n k : Nat} [NeZero n] [NeZero k] {inputs inputs' : List (RewriteName χ)} {output : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.order n) inputs [output]))
    (h₂ : aps[i₂]? = some (.async (.sink k) inputs' []))
    (hne : i₂ ≠ i₁)
    (hn : n > 1) (hlen : inputs.length = n) (hlen' : inputs'.length = k)
    (hmem : output ∈ inputs') :
    DCEMatch aps [i₂, i₁] "order-sink" [
      .sink inputs.toVector,
      .sink (inputs'.erase output).toVector,
    ]
  | order_const
    {n : Nat} [NeZero n] {first output act output' : RewriteName χ} {rest : List (RewriteName χ)} {v : V}
    [NeZero ((first :: rest).erase output' ++ [act]).length]
    (h₁ : aps[i₁]? = some (.async (.order n) (first :: rest) [output]))
    (h₂ : aps[i₂]? = some (.async (.const v 1) [act] [output']))
    (hne : i₂ ≠ i₁)
    (hn : n > 1) (hlen : (first :: rest).length = n)
    (hmem : output' ∈ rest) (hne' : output' ≠ first) :
    DCEMatch aps [i₂, i₁] "order-const" [
      .order ((first :: rest).erase output' ++ [act]).toVector output,
    ]
  | order_const_head
    {n : Nat} [NeZero n] {output act output' : RewriteName χ} {rest : List (RewriteName χ)} {v : V}
    [NeZero (act :: rest).length]
    (h₁ : aps[i₁]? = some (.async (.order n) (output' :: rest) [output]))
    (h₂ : aps[i₂]? = some (.async (.const v 1) [act] [output']))
    (hne : i₂ ≠ i₁)
    (hn : n > 1) (hlen : (output' :: rest).length = n) :
    DCEMatch aps [i₂, i₁] "order-const-head" [
      .order (act :: rest).toVector output',
      .const v output' #v[output],
    ]
  | order_steer_steer
    {flavor : Bool} {orderInput₁ orderInput₂ output decider₁ input₁ decider₂ input₂ : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.order 2) [orderInput₁, orderInput₂] [output]))
    (h₂ : aps[i₂]? = some (.async (.steer flavor 1) [decider₁, input₁] [orderInput₁]))
    (h₃ : aps[i₃]? = some (.async (.steer flavor 1) [decider₂, input₂] [orderInput₂]))
    (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
    (hfork : SameFork aps decider₁ decider₂) :
    DCEMatch aps [i₃, i₂, i₁] "order-steer-steer" [
      .order #v[input₁, input₂] orderInput₁,
      .steer flavor decider₁ #v[orderInput₁] #v[output],
      .sink #v[decider₂],
    ]
  | const_sink
    {act output : RewriteName χ} {v : V}
    (h₁ : aps[i₁]? = some (.async (.const v 1) [act] [output]))
    (h₂ : aps[i₂]? = some (.async (.sink 1) [output] []))
    (hne : i₂ ≠ i₁) :
    DCEMatch aps [i₂, i₁] "const-sink" [.sink #v[act]]
  | inact_sink
    {n k : Nat} [NeZero k] {outputs inputs' : List (RewriteName χ)}
    (h₁ : aps[i₁]? = some (.async (.inact n) [] outputs))
    (h₂ : aps[i₂]? = some (.async (.sink k) inputs' []))
    (hne : i₂ ≠ i₁)
    (hn : n > 0) (hlen : outputs.length = n) (hlen' : inputs'.length = k)
    (hndisj : ¬ outputs.Disjoint inputs') :
    DCEMatch aps [i₂, i₁] "inact-sink" [
      .inact (outputs.removeAll inputs').toVector,
      .sink (inputs'.removeAll outputs).toVector,
    ]
  | carry_fork_steer_to_inv_left
    {decider inputL inputR output output₁' output₂' decider'' : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.merge .popLeft 1) [decider, inputL, inputR] [output]))
    (h₂ : aps[i₂]? = some (.async (.fork 2) [output] [output₁', output₂']))
    (h₃ : aps[i₃]? = some (.async (.steer true 1) [decider'', output₁'] [inputR]))
    (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
    (hfork : SameFork aps decider decider'') :
    DCEMatch aps [i₃, i₂, i₁] "carry-fork-steer-to-inv-left" [
      .inv true none decider inputL output₂',
      .sink #v[decider''],
    ]
  | carry_fork_steer_to_inv_right
    {decider inputL inputR output output₁' output₂' decider'' : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.merge .popLeft 1) [decider, inputL, inputR] [output]))
    (h₂ : aps[i₂]? = some (.async (.fork 2) [output] [output₁', output₂']))
    (h₃ : aps[i₃]? = some (.async (.steer true 1) [decider'', output₂'] [inputR]))
    (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
    (hne : output₂' ≠ output₁')
    (hfork : SameFork aps decider decider'') :
    DCEMatch aps [i₃, i₂, i₁] "carry-fork-steer-to-inv-right" [
      .inv true none decider inputL output₁',
      .sink #v[decider''],
    ]
  | carry_steer_cycle_to_sink
    {decider inputL inputR output decider' : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.merge .popLeft 1) [decider, inputL, inputR] [output]))
    (h₂ : aps[i₂]? = some (.async (.steer true 1) [decider', output] [inputR]))
    (hne : i₂ ≠ i₁)
    (hfork : SameFork aps decider decider') :
    DCEMatch aps [i₂, i₁] "carry-steer-cycle-to-sink" [.sink #v[decider, decider', inputL]]
  | carry_order_steer_cycle_to_sink
    {k : Nat} [NeZero k] {decider inputL inputR output decider' output' : RewriteName χ} {inputs'' : List (RewriteName χ)}
    (h₁ : aps[i₁]? = some (.async (.merge .popLeft 1) [decider, inputL, inputR] [output]))
    (h₂ : aps[i₂]? = some (.async (.steer true 1) [decider', output] [output']))
    (h₃ : aps[i₃]? = some (.async (.order k) inputs'' [inputR]))
    (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
    (hlen : inputs''.length = k)
    (hmem : output' ∈ inputs'')
    (hfork : SameFork aps decider decider') :
    DCEMatch aps [i₃, i₂, i₁] "carry-order-steer-cycle-to-sink" [
      .sink (#v[decider, decider', inputL] ++ (inputs''.erase output').toVector),
    ]
  | carry_false
    {decider inputL inputR output : RewriteName χ} {v : V}
    (h₁ : aps[i₁]? = some (.async (.merge .popLeft 1) [decider, inputL, inputR] [output]))
    (hconst : FromConst aps decider v)
    (hbool : InterpConsts.toBool v = some false) :
    DCEMatch aps [i₁] "carry-false" [
      .forward #v[inputL] #v[output],
      .sink #v[decider],
      .sink #v[inputR],
    ]
  | carry_true
    {decider inputL inputR output : RewriteName χ} {v : V}
    (h₁ : aps[i₁]? = some (.async (.merge .popRight 1) [decider, inputL, inputR] [output]))
    (hconst : FromConst aps decider v)
    (hbool : InterpConsts.toBool v = some true) :
    DCEMatch aps [i₁] "carry-true" [
      .forward #v[inputR] #v[output],
      .sink #v[decider],
      .sink #v[inputL],
    ]
  | merge_sink
    {k : Nat} [NeZero k] {decider inputL inputR output : RewriteName χ} {inputs' : List (RewriteName χ)}
    (h₁ : aps[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
    (h₂ : aps[i₂]? = some (.async (.sink k) inputs' []))
    (hne : i₂ ≠ i₁)
    (hlen : inputs'.length = k)
    (hmem : output ∈ inputs') :
    DCEMatch aps [i₂, i₁] "merge-sink" [
      .sink #v[decider],
      .sink #v[inputL],
      .sink #v[inputR],
      .sink (inputs'.erase output).toVector,
    ]
  | merge_steer_true
    {decider inputL inputR output decider' output' : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
    (h₂ : aps[i₂]? = some (.async (.steer true 1) [decider', output] [output']))
    (hne : i₂ ≠ i₁)
    (hfork : SameFork aps decider decider') :
    DCEMatch aps [i₂, i₁] "merge-steer-true" [
      .forward #v[inputR] #v[output'],
      .sink #v[decider, decider', inputL],
    ]
  | merge_steer_false
    {decider inputL inputR output decider' output' : RewriteName χ}
    (h₁ : aps[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
    (h₂ : aps[i₂]? = some (.async (.steer false 1) [decider', output] [output']))
    (hne : i₂ ≠ i₁)
    (hfork : SameFork aps decider decider') :
    DCEMatch aps [i₂, i₁] "merge-steer-false" [
      .forward #v[inputL] #v[output'],
      .sink #v[decider, decider', inputR],
    ]
  | merge_dedup
    {k : Nat} {decider inputL inputR output decider' inputL' inputR' output' : RewriteName χ}
    {inputs₀ outputs₀ : List (RewriteName χ)}
    (h₁ : aps[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
    (h₂ : aps[i₂]? = some (.async (.fork k) inputs₀ outputs₀))
    (h₃ : aps[i₃]? = some (.async (.merge .decider 1) [decider', inputL', inputR'] [output']))
    (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
    (hfork₁ : SameFork aps decider decider')
    (hfork₂ : SameFork aps inputL inputL')
    (hfork₃ : SameFork aps inputR inputR') :
    DCEMatch aps [i₃, i₂, i₁] "merge-dedup" [
      .async (.fork k) inputs₀ outputs₀,
      .merge decider #v[inputL] #v[inputR] #v[.rename 0 output],
      .fork (.rename 0 output) #v[output, output'],
      .sink #v[decider', inputL', inputR'],
    ]
  | merge_same_const
    {decider inputL inputR output input₁ input₂ : RewriteName χ} {v : V}
    (h₁ : aps[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
    (h₂ : aps[i₂]? = some (.async (.const v 1) [input₁] [inputL]))
    (h₃ : aps[i₃]? = some (.async (.const v 1) [input₂] [inputR]))
    (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂) :
    DCEMatch aps [i₃, i₂, i₁] "merge-same-const" [
      .merge decider #v[input₁] #v[input₂] #v[.rename 0 input₁],
      .const v (.rename 0 input₁) #v[output],
    ]
  | merge_true_false_const
    {decider inputL inputR output input₁ input₂ : RewriteName χ} {v₁ v₂ : V}
    (h₁ : aps[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
    (h₂ : aps[i₂]? = some (.async (.const v₁ 1) [input₁] [inputL]))
    (h₃ : aps[i₃]? = some (.async (.const v₂ 1) [input₂] [inputR]))
    (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
    (hbool₁ : InterpConsts.toBool v₁ = some false)
    (hbool₂ : InterpConsts.toBool v₂ = some true) :
    DCEMatch aps [i₃, i₂, i₁] "merge-true-false-const" [
      .forward #v[decider] #v[output],
      .sink #v[input₁],
      .sink #v[input₂],
    ]
  /-- Rules that are not forward simulations; no information is kept. -/
  | excluded (h : name ∈ excludedRules) : DCEMatch aps matched name res

end Wavelet.Compile.DeadCodeElim
