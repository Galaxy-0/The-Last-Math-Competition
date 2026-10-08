# Conjecture 00000002753: An infinite-dimensional algebra satisfies a nontrivial nested identity

The actual algebra Q[T] is not a finite Q-module and satisfies [[X,Y],Z]=0 for every substitution. That free associative polynomial is nonzero, as its evaluation at E01, E10, E01 in M2(Q) is 2E01.

## Scope

The polynomial is genuinely nested with two commutator operations. Nontrivial means nonzero in the free associative algebra, not nonzero after substitution in the algebra satisfying the identity. The example is unital, nonzero and in characteristic zero. The source places no noncommutativity restriction on its infinite-dimensional algebras. The matrix-algebra minimal-length clause is not addressed.

See `main.tex` and `main.pdf` for the full proof and exact Lean correspondence. `SOURCE.md` preserves the bilingual conjecture.

## Reproduction and verification

In `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned. The manifest pins all transitive dependencies and contains no local paths. A new machine can fetch official dependency artifacts with `lake exe cache get`. From the submission directory, run `tectonic main.tex` to export the PDF. Run `python verify.py` for exact free-word and matrix checks.

The project's own artifacts are rebuilt from scratch; only verified official dependency artifacts are reused. Actual logs, source hashes, standard axiom checks and PDF inspections are recorded in `verification/`. Separate author self-review and delegated-agent adversarial review are included. No external independent review is claimed.
