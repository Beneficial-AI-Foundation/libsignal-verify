import Lake
open Lake DSL

-- The book reads the Lean development of the enclosing repository. Its pins
-- (Lean, VCVio, Mathlib, Aeneas) come from the root package's manifest.
require Libsignal from ".."
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"4943d3335ffa9221a39949e60836a8ad5dc2a456"

package LibsignalVerifyBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_lib LibsignalVerifyBlueprint
