import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

package wavelet

lean_lib Wavelet where
  defaultFacets := #[LeanLib.staticFacet]

@[default_target]
lean_exe wavelet where
  root := `Main
  needs := #[Wavelet]
  moreLinkArgs :=
    if System.Platform.isOSX then
      #[
        "-dead_strip",
        "-dead_strip_dylibs",
        "-Wl,--icf=all",
        "-Wl,-x",
        "-Wl,-S",
      ]
    else if System.Platform.isWindows then
      #[]
    else
      #[
        "-Wl,--gc-sections",
        "-Wl,--icf=all",
        "-Wl,--strip-all",
        "-Wl,--strip-debug",
      ]

lean_lib Thm where
  roots := #[`Wavelet.Thm]
  defaultFacets := #[LeanLib.leanArtsFacet]
