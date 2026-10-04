# Disproof of 00000008492

On the one-point probability space with the identity transformation, let `X_n = sqrt(n)`. This is an actual nonnegative integrable subadditive process over an ergodic probability-preserving system. Its normalized expectation is `1/sqrt(n)` for positive indices and converges to zero, but is not `O(log(n)/n)`.

The Lean theorem `no_eventual_rate` proves that for every real constant C and every starting index N, some n ≥ max(N,1) has `C * (log(n)/n) < E[X_n]/n`. The theorem `not_bigO` proves the negation using Mathlib's actual norm-based big-O definition.

Files:

- `report.tex` and `report.pdf`: complete proof, scope, and formal correspondence.
- `lean/Main.lean`: actual Dirac probability measure, ergodicity, Bochner integrals, subadditive inequality with iterates, normalized convergence, and asymptotic contradiction.
- `lean/lakefile.lean`, `lean/lake-manifest.json`, `lean/lean-toolchain`: public pinned Lean 4.19.0 / Mathlib project.
- `VERIFICATION.md`: validation and eligibility evidence.

From `lean/`, run `lake update`, `lake exe cache get`, `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. Local dependency junctions and build products are ignored. Only standard logical axioms occur in the six printed audits.

Both original language versions claim a universal logarithmic-harmonic upper rate for random subadditive sequences. No uniform bound on the unnormalized process is specified. Each variable in this example is bounded, and the normalized process is uniformly bounded for positive indices. The disproof permits process-dependent constants and starting indices; it does not merely violate a fixed coefficient.

The editor was opened and its compiler attempted; the environment returned its platform-directory error. The delivered PDF was compiled with Tectonic and all pages were visually inspected.
