# Disprove conjecture 00000007792: the M-ellipsoid constant is at least 4, not at most (π/4)e

- **Witness.** The Euclidean unit ball B in ℝⁿ, in every dimension n ≥ 1.
- **Bound.** For every ellipsoid E = c + A·B (A invertible, any centre), vol(B + E)·vol(B° + E°) ≥ 4ⁿ·vol(B)·vol(B°). Proof via the eigenbasis of A*A: B + E contains D_{1+s}B, B + E° contains a translate of D_{1+1/s}B, and (1+s)(1+1/s) ≥ 4; non-centred ellipsoids are handled by a translation argument.
- **Consequence.** Every admissible constant has |C| ≥ 4 (C ≥ 4 in odd dimensions), while (π/4)e ≈ 2.135.
- **Refuted readings.** A single C in all dimensions (`conjecture_7792_false`), in all large dimensions (`conjecture_7792_false_eventually`), and limits of per-dimension constants C_n ≥ 0 (`conjecture_7792_false_limit`), with C^n as the Definition line writes it.
- **Not refuted.** A C^{2n} normalization (our bound then gives only C ≥ 2); the stability (e^{cd²}) conjunct is not addressed — refuting the first conjunct refutes the conjunction.
- **Conventions.** Ellipsoids are non-degenerate; polarity is with respect to the origin; "optimal constant" is handled by proving every admissible C satisfies |C| ≥ 4.
- **Main theorems.** `Conjecture7792.conjecture_7792_false`, `Conjecture7792.admissible_abs_ge_four`, `Conjecture7792.ball_volume_product_ge`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 332 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7792/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007792.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture7792.conjecture_7792_false`, `Conjecture7792.admissible_abs_ge_four`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007792 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
