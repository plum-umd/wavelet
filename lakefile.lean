import Lake
open Lake DSL

package «wavelet» where
  -- add package configuration options here

lean_lib «Wavelet» where
  -- add library configuration options here

@[default_target]
lean_exe «wavelet» where
  root := `Main
