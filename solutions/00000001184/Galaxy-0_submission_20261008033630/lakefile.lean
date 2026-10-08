import Lake
open Lake DSL
package «tlmc1184» where
  leanOptions := #[⟨`warningAsError, true⟩]
@[default_target]
lean_lib Counterexample
