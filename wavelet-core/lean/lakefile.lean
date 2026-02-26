import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

package wavelet

@[default_target]
lean_lib Wavelet where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib Thm where
  roots := #[`Wavelet.Thm]
  defaultFacets := #[LeanLib.leanArtsFacet]
