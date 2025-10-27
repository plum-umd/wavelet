import Wavelet.Dataflow.Proc
import Wavelet.Determinacy.OpSpec

/-! Definitions for mapping tokens through a PCM homomorphism. -/

namespace Wavelet.Determinacy

open Semantics

/-- Map permission tokens in the spec through a PCM map. -/
def OpSpec.mapTokens
  [Arity Op]
  (opSpec : OpSpec Op V T₁)
  (hom : T₁ → T₂) : OpSpec Op V T₂ := {
    pre op inputs := hom (opSpec.pre op inputs),
    post op inputs outputs := hom (opSpec.post op inputs outputs),
  }

def IOSpec.mapTokens
  (ioSpec : IOSpec V T₁ m n)
  (hom : T₁ → T₂) : IOSpec V T₂ m n := {
    pre vals := hom (ioSpec.pre vals),
    post vals := hom (ioSpec.post vals),
  }

end Wavelet.Determinacy

namespace Wavelet.Dataflow

open Semantics Determinacy

def AsyncOp.mapValues
  (f : V₁ → V₂) : AsyncOp V₁ → AsyncOp V₂
  | .switch n => .switch n
  | .steer flavor n => .steer flavor n
  | .merge state n => .merge state n
  | .forward n => .forward n
  | .fork n => .fork n
  | .const c n => .const (f c) n
  | .forwardc n m consts => .forwardc n m (consts.map f)
  | .sink n => .sink n

def AtomicProc.mapTokens
  [Arity Op]
  {opSpec : OpSpec Op V T₁}
  (hom : T₁ → T₂) :
  AtomicProc (WithSpec Op opSpec) χ (V ⊕ T₁) → AtomicProc (WithSpec Op (opSpec.mapTokens hom)) χ (V ⊕ T₂)
  | .op (.op o) inputs outputs => .op (.op o) inputs outputs
  | .op (.join k l req) inputs outputs => .op (.join k l (hom ∘ req)) inputs outputs
  | .async o inputs outputs =>
    .async (o.mapValues mapValue) inputs outputs
  where
    mapValue : V ⊕ T₁ → V ⊕ T₂
      | .inl v => .inl v
      | .inr t => .inr (hom t)

def AtomicProcs.mapTokens
  [Arity Op]
  {opSpec : OpSpec Op V T₁}
  (hom : T₁ → T₂)
  (aps : AtomicProcs (WithSpec Op opSpec) χ (V ⊕ T₁)) :
    AtomicProcs (WithSpec Op (opSpec.mapTokens hom)) χ (V ⊕ T₂)
  := aps.map (.mapTokens hom)

/-- Map the tokens through a PCM map. Note that on a well-formed
process, this should not change anything, since we should not have
token constants in the processes. -/
def Proc.mapTokens
  [Arity Op]
  {opSpec : OpSpec Op V T₁}
  (hom : T₁ → T₂)
  (proc : ProcWithSpec opSpec χ m n) :
    ProcWithSpec (OpSpec.mapTokens opSpec hom) χ m n
  := {
    inputs := proc.inputs,
    outputs := proc.outputs,
    atoms := proc.atoms.mapTokens hom,
  }

end Wavelet.Dataflow
