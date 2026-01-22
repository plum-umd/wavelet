import Wavelet.Data.IndentWriter
import Wavelet.Frontend.RipTide

/-!
A (unverified) backend that compiles RipTide dataflow graphs
to a dataflow circuit in the CIRCT Handshake dialect.
-/

namespace Wavelet.Backend.Handshake

open Frontend Semantics Dataflow

abbrev EmitM := IndentWriterT Unit String

end Wavelet.Backend.Handshake
