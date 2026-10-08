# Conjecture 00000000320: Cantor and Hall-ray properties are incompatible

The source assigns total disconnectedness (as a Cantor set) and a contained Hall half-line to the same real set. A nondegenerate connected interval inside the half-line contradicts total disconnectedness. A separate proof uses nowhere density.

## Scope

This refutes a conjunction of necessary topological properties for every real set. It does not compute or replace the actual restricted Markov spectrum, nor assume it is Cantor. Both endpoint conventions and the endpoint-before-4 condition are covered. A statement about sums of Cantor sets would be different.

See `main.tex` and `main.pdf` for the full proof and exact Lean correspondence. `SOURCE.md` preserves the bilingual conjecture.

## Reproduction and verification

In `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned. The manifest pins all transitive dependencies and contains no local paths. A new machine can fetch official dependency artifacts with `lake exe cache get`. From the submission directory, run `tectonic main.tex` to export the PDF. No auxiliary numerical computation is needed.

The project's own artifacts are rebuilt from scratch; only verified official dependency artifacts are reused. Actual logs, source hashes, standard axiom checks and PDF inspections are recorded in `verification/`. Separate author self-review and delegated-agent adversarial review are included. No external independent review is claimed.
