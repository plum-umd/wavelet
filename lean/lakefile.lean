import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

package wavelet

@[default_target]
lean_lib Wavelet

@[default_target]
lean_exe wavelet where
  root := `Main
