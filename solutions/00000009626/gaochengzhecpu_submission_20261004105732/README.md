# Conjecture 00000009626 — Disproof

The two-dimensional full shift on three symbols is an SFT with no forbidden
patterns. It has exactly `3^(n*n)` occurring square patterns and spatial entropy
`log 3 > log 2`. The source does not restrict the alphabet to two symbols.

## Reproduce

With Lean 4.19.0 (see `lean-toolchain`), from `lean/`:

```sh
lake update
lake exe cache get Mathlib/Analysis/SpecialFunctions/Log/Basic.lean Mathlib/Data/Fintype/Pi.lean Mathlib/Data/Fintype/Prod.lean Mathlib/Tactic/NormNum.lean Mathlib/Tactic/Positivity.lean Mathlib/Tactic/Ring.lean Mathlib/Tactic/FieldSimp.lean
lake build
lake env lean -DwarningAsError=true Main.lean
```

Mathlib and transitive dependencies are pinned in `lake-manifest.json`; Mathlib
is commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0). Standard
foundational axiom dependencies are printed at the end of the Lean file.
No additional axioms or admitted results are introduced.

From the submission directory:

```sh
python verify.py
tectonic main.tex
```

The Python script supplements the proof with finite enumeration; it does not
establish the all-size result. Lean proves the pattern extension, exact count,
real logarithmic expression, convergence, and strict entropy-bound violation.
`HasSpatialEntropy` is the standard square-box pattern-count limit, reindexed
by side length `n+1` so that boxes are nonempty.

`SOURCE.md` preserves the source conjecture. `verification/BUILD.json` and logs
record actual commands, hashes, dependency versions, and PDF checks.
`verification/SELF_REVIEW.md` is an adversarial self-review by the same agent,
not independent review. AI-assisted submission by gaochengzhecpu.
