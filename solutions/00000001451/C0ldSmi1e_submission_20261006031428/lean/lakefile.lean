import Lake
open Lake DSL
package tlmc1451 where
  leanOptions := #[⟨`warningAsError, true⟩]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"
lean_lib Geometry
lean_lib Vanishing
@[default_target] lean_lib Solution
