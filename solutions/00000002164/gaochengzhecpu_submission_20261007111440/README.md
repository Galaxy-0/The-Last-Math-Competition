# Conjecture 00000002164: positive 2-factor counts cannot decay to zero

The connected prism graphs C_m square K_2 have 2m vertices, degree three, and a spanning 2-factor consisting of their two cycle layers. Thus their actual 2-factor counts are at least one. Since 4^(1/3)/pi < 1, the proposed expression tends to zero, and these counts are not even O of that expression.

## Scope

The source gives no normalization, averaging law or further graph restriction. This submission refutes its literal unnormalized 2-factor counting assertion along an infinite family of connected simple cubic graphs. It does not evaluate a differently normalized count, probability or ensemble average, and does not assume that every cubic graph has a 2-factor. See `main.tex` and `main.pdf` for the proof and exact Lean correspondence. `SOURCE.md` preserves the bilingual conjecture.

## Reproduction and verification

In `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned. The manifest pins all transitive dependencies using public Git URLs without local paths. A new machine can fetch official dependency artifacts with `lake exe cache get`. From the submission directory, run `tectonic main.tex` to export the PDF. No auxiliary numerical computation is needed.

The project's own artifacts are rebuilt from scratch; only verified official dependency artifacts are reused. Actual logs, source hashes, standard axiom checks and PDF inspections are recorded in `verification/`. Separate author self-review and delegated-agent adversarial review are included. No external independent review is claimed.
