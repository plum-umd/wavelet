import Mathlib.Control.Monad.Writer

import Wavelet.Dataflow.Proc

/-! Some utilities to generate Graphviz's DOT format. -/

namespace Wavelet.Dataflow

open Semantics

structure PlotState where
  indent : Nat

def PltoState.init : PlotState := { indent := 0 }

abbrev PlotM := WriterT (List String) (StateT PlotState (Except String))

def PlotM.startBlock (cmd : String) : PlotM Unit := do
  let s ← get
  tell [String.replicate (s.indent * 2) ' ' ++ cmd ++ " {"]
  modify λ s => { s with indent := s.indent + 1 }

def PlotM.endBlock : PlotM Unit := do
  let s ← get
  if s.indent = 0 then
    throw "no matching left brace"
  tell [String.replicate (s.indent * 2 - 2) ' ' ++ "}"]
  modify λ s => { s with indent := s.indent - 1 }

def PlotM.cmd (cmd : String) : PlotM Unit := do
  let s ← get
  tell [String.replicate (s.indent * 2) ' ' ++ cmd]

/-- Generates the final plot in DOT format. -/
def PlotM.run (plot : PlotM Unit) : Except String String := do
  let ((_, cmds), _) ← (WriterT.run plot).run PltoState.init
  return String.intercalate "\n" cmds

/-- Find sender(s) of a channel name. -/
def Proc.sendersOf [Arity Op] [DecidableEq χ]
  (proc : Proc Op χ V m n) (chan : χ) : List (Nat × AtomicProc Op χ V) :=
  (proc.atoms.mapIdx (·, ·)).filter λ (_, atom) => chan ∈ atom.outputs

/-- Find receiver(s) of a channel name. -/
def Proc.receiversOf [Arity Op] [DecidableEq χ]
  (proc : Proc Op χ V m n) (chan : χ) : List (Nat × AtomicProc Op χ V) :=
  (proc.atoms.mapIdx (·, ·)).filter λ (_, atom) => chan ∈ atom.inputs

class DotName Op where
  dotName : Op → String

def AtomicProc.dotAttrs [Arity Op] [DotName Op] [DotName V] : AtomicProc Op χ V → String
  | .op o .. => s!"label={DotName.dotName o} shape=circle fixedsize=true height=0.6 width=0.6"
  | .async (.switch _) .. => s!"label=\"S\" shape=triangle fixedsize=true height=0.6 width=0.513 style=filled fillcolor=lightgrey"
  | .async (.steer flavor _) .. =>
    let color := if flavor then "lightgreen" else "indianred2"
    s!"label=\"\" shape=triangle fixedsize=true height=0.3 width=0.256 style=filled fillcolor={color}"
  | .async (AsyncOp.merge state _) .. =>
    let label := match state with
      | .popLeft => "C" -- Carry (true)
      | .popRight => "C'" -- Carry (false)
      | .decider => "M" -- Merge
    s!"label=\"{label}\" shape=triangle orientation=180 fixedsize=true height=0.6 width=0.513 style=filled fillcolor=lightgrey"
  | .async (AsyncOp.forward _) .. =>
    s!"label=\"id\" shape=square fixedsize=true height=0.5 width=0.5 style=filled fillcolor=lightgrey"
  | .async (AsyncOp.fork _) .. =>
    s!"shape=point"
  | .async (AsyncOp.order _) .. =>
    s!"label=\"O\" shape=square fixedsize=true height=0.5 width=0.5 style=filled fillcolor=lightgrey"
  | .async (AsyncOp.const v _) .. =>
    s!"label={DotName.dotName v} shape=square fixedsize=true height=0.27 width=0.27"
  | .async (AsyncOp.forwardc _ _ _) .. =>
    s!"label=\"idc\" shape=square fixedsize=true height=0.5 width=0.5 style=filled fillcolor=lightgrey"
  | .async (AsyncOp.sink _) .. =>
    s!"label=\"⊥\" shape=square fixedsize=true height=0.5 width=0.5 style=filled fillcolor=lightgrey"
  | .async AsyncOp.inact .. =>
    s!"label=\"⊥\" shape=square fixedsize=true height=0.5 width=0.5 style=filled fillcolor=lightgrey"

/-- Generates the port name for a particular input index. -/
def Proc.plot.inputPortName
  [Arity Op] [DecidableEq χ]
  (ap : AtomicProc Op χ V) (portIdx : Nat) : String :=
  match ap with
  | .async (.steer _ 1) ..
  | .async (.switch 1) .. =>
    if portIdx = 0 then "e" -- Decider
    else "n" -- Input
  | .async (.merge _ 1) .. =>
    match portIdx with
    | 0 => "e" -- Decider
    | 1 => "nw" -- Input 1
    | _ => "ne" -- Input 2
  | _ =>
    match ap.inputs.length with
    | 2 => ["nw", "ne"][portIdx]?.getD "n"
    | 3 => ["nw", "n", "ne"][portIdx]?.getD "n"
    | 4 => ["w", "nw", "n", "ne"][portIdx]?.getD "n"
    | _ => "n"

/-- Generates the port name for a particular output index. -/
def Proc.plot.outputPortName
  [Arity Op] [DecidableEq χ]
  (ap : AtomicProc Op χ V) (portIdx : Nat) : String :=
  match ap.outputs.length with
  | 2 => ["sw", "se"][portIdx]?.getD "s"
  | 3 => ["sw", "s", "se"][portIdx]?.getD "s"
  | 4 => ["sw", "s", "se", "e"][portIdx]?.getD "s"
  | _ => "s"

/-- Plot the dataflow graph in DOT format. -/
def Proc.plot
  [Arity Op] [DotName Op] [DotName V] [Repr χ]
  [DecidableEq χ]
  (proc : Proc Op χ V m n) : PlotM Unit := do
  .startBlock "digraph G"
  .cmd r#"graph [fontname="courier"]"#
  .cmd r#"node [fontname="courier"]"#
  .cmd r#"edge [fontname="courier" fontsize=10]"#

  -- Draw nodes for inputs and outputs
  for i in [0:m] do
    PlotM.cmd s!"i{i} [label=\"Input {i}\" tailport=s shape=box style=\"rounded,filled\" fillcolor=\"lightskyblue1\"]"

  for i in [0:n] do
    PlotM.cmd s!"o{i} [label=\"Output {i}\" headport=n shape=box style=\"rounded,filled\" fillcolor=\"lightskyblue1\"]"

  -- Emit all nodes
  for (i, atom) in proc.atoms.mapIdx (·, ·) do
    PlotM.cmd s!"a{i} [{atom.dotAttrs}]"

  -- Iterate through all atoms and draw edges
  for (idx₁, atom) in proc.atoms.mapIdx (·, ·) do
    -- Draw edges to input ports
    for (inPort₁, chan) in atom.inputs.mapIdx (·, ·) do
      let headPort := plot.inputPortName atom inPort₁

      let senders := proc.sendersOf chan
      for (idx₂, sender) in senders do
        for (outPort₂, chan') in sender.outputs.mapIdx (·, ·) do
          if chan = chan' then
            -- Draw an edge from (idx₂, outPort₂) to (idx₁, inPort₁)
            let tailPort := plot.outputPortName sender outPort₂
            PlotM.cmd s!"a{idx₂} -> a{idx₁} [arrowsize=0.4 headport={headPort} tailport={tailPort}]"

      -- Also draw edges from process inputs
      if chan ∈ proc.inputs then
        for inputIdx in List.finRange m do
          if chan = proc.inputs[inputIdx] then
            -- Draw an edge from inputIdx to (idx₁, inPort₁)
            PlotM.cmd s!"i{inputIdx} -> a{idx₁} [arrowsize=0.4 tailport=s headport={headPort}]"
      else if senders.isEmpty then
        -- Special annotation for dangling inputs
        PlotM.cmd s!"c{idx₁}i{inPort₁} [label=\"?\" shape=plaintext]"
        PlotM.cmd s!"c{idx₁}i{inPort₁} -> a{idx₁} [arrowsize=0.4 headport={headPort}]"

    -- Draw edges from output ports
    for (outPort₁, chan) in atom.outputs.mapIdx (·, ·) do
      let tailPort := plot.outputPortName atom outPort₁

      let receivers := proc.receiversOf chan

      -- No need to draw edges to the receivers, since they should have been added already
      -- for (idx₂, receiver) in receivers do
      --   for (inPort₂, chan') in receiver.inputs.mapIdx (·, ·) do
      --     if chan = chan' then
      --       -- Draw an edge from (idx₁, outPort₁) to (idx₂, inPort₂)
      --       let headPort := plot.inputPortName receiver inPort₂
      --       PlotM.cmd s!"a{idx₁} -> a{idx₂} [arrowsize=0.4 headport={headPort} tailport={tailPort}]"

      -- Also draw edges to process outputs
      if chan ∈ proc.outputs then
        for outputIdx in List.finRange n do
          if chan = proc.outputs[outputIdx] then
            -- Draw an edge from (idx₁, outPort₁) to outputIdx
            PlotM.cmd s!"a{idx₁} -> o{outputIdx} [arrowsize=0.4 headport=n tailport={tailPort}]"
      else if receivers.isEmpty then
        -- Special annotation for dangling outputs
        PlotM.cmd s!"c{idx₁}o{outPort₁} [label=\"?\" shape=plaintext]"
        PlotM.cmd s!"c{idx₁}o{outPort₁} -> a{idx₁} [arrowsize=0.4 tailPort={tailPort}]"

  .endBlock

end Wavelet.Dataflow
