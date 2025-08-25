import Lake
open Lake DSL

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.22.0"

package «wavelet» where
  -- add package configuration options here

lean_lib «Wavelet» where
  -- add library configuration options here

@[default_target]
lean_exe «wavelet» where
  root := `Main
