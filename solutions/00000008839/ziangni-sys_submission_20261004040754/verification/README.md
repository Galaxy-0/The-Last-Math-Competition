# Completed verification

A fresh complete local project build passed (`lean-build.txt`). Direct checking of the entire final Main.lean with warnings treated as errors passed (`lean-check.txt`). Six audited results use only propext, Classical.choice and Quot.sound. No admitted proofs, custom axioms or native decision shortcuts are used. Exact real algebra and actual CLM norms are kernel checked; no auxiliary numerical program is necessary.

Tectonic compiled the final two-page A4 PDF without boxwarnings (`pdf-build.txt`). Both pages were rendered with Poppler at1400pixels and visually inspected in full: clear formulas/layout, no clipping/overlap. The built-in LaTeX editor/compiler were used; compiler returned known platform standard-directory lookup failure, but actual PDF compilation succeeded using Tectonic.

`source.md` preserves both original languages and `eligibility.txt` records initial checks. Scope is the always-lambda-times-norm error clause, refuted even if interpreted as an upper bound or pointwise unit-vector estimate. Actual A=4id, positive lambda=1/4, actual resolvent halfid and standard Yosida definition are proved; actual error norm2 exceeds product1. The separate approximate-solution convergence clause is not addressed. The explanatory general scalar formula in the report is not required by the concrete formal disproof.

No dependency cache writes occurred; the public Lean project pins Git revisions rather than local paths. Build artifacts and local cache junctions are ignored.
