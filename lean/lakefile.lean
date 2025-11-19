import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

package wavelet

-- Check all proofs
lean_lib Wavelet

@[default_target]
lean_exe wavelet where
  root := `Main
