import Wavelet.Semantics.Defs
import Wavelet.Semantics.OpInterp

/-! Reasoning about the determinancy of semantics. -/

namespace Wavelet.Semantics

open Semantics

abbrev CompatRel V := ∀ {n m}, Vector V n → Vector V m → Prop

/-- Any yielding transitions from the same state commute,
if a certain compatibility constraint holds on the inputs. -/
def CommYields
  [Arity Op]
  (Compat : CompatRel V)
  (sem : Semantics Op V m n)
  : Prop :=
  ∀ s s₁ s₂
    op₁ inputs₁ outputs₁
    op₂ inputs₂ outputs₂,
    sem.lts.Step s (.yield op₁ inputs₁ outputs₁) s₁ →
    sem.lts.Step s (.yield op₂ inputs₂ outputs₂) s₂ →
    Compat inputs₁ inputs₂ →
    ∃ s',
      sem.lts.Step s₁ (.yield op₂ inputs₂ outputs₂) s' ∧
      sem.lts.Step s₂ (.yield op₁ inputs₁ outputs₁) s'

def OpInterp.Determinant
  [Arity Op]
  (Compat : CompatRel V)
  (interp : OpInterp Op V)
  : Prop :=
  ∀ s s₁ s₂
    op₁ inputs₁ outputs₁
    op₂ inputs₂ outputs₂,
    interp.interp op₁ inputs₁ s outputs₁ s₁ →
    interp.interp op₂ inputs₂ s outputs₂ s₂ →
    Compat inputs₁ inputs₂ →
    ∃ s',
      interp.interp op₁ inputs₁ s₂ outputs₁ s' ∧
      interp.interp op₂ inputs₂ s₁ outputs₂ s'

end Wavelet.Semantics
