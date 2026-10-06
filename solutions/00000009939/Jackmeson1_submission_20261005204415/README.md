# Disprove conjecture 00000009939: entropy minus the longest bar's contribution can exceed (1/2) log(#bars)

- **Reading.** Persistence entropy E = −Σ p_i log p_i with p_i = ℓ_i/L over the finite bars, counted with multiplicity (Atienza et al.; arXiv 1701.07857 and 1803.08304, retrieved and quoted). The Chinese text fixes the subtracted term as the longest bar's own summand −p_max log p_max. Refuted claim: E − c(I) ≤ (1/2) log n for every nonempty barcode and every longest bar I.
- **Counterexample.** Bars [0,2), [0,1), [1,2): E − c = log 2 ≈ 0.693 > (1/2) log 3 ≈ 0.549 (`conjecture9939_false`). The filter's equal-bar witnesses are not used.
- **Robustness.** The bound fails for every bar count n ≥ 2 with pairwise distinct bars and a unique longest bar (`bound_fails_every_count`); no constant c < 1 can replace 1/2 (`no_constant_below_one`); the binary-entropy reading h(p_max) and the −log p_max reading also fail (`binary_reading_false`, `minEntropy_reading_false`).
- **Scope.** Barcodes are abstract finite multisets of bars (Mathlib has no persistent homology); a filtration realizing any barcode (a wedge of hollow triangles, degree 1) is given in prose. Infinite bars are excluded, as in the cited definition. The "concentration inequalities" conjunct is not addressed; refuting one conjunct refutes the conjecture.
- **Main theorem.** `Conjecture9939.conjecture9939_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 296 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture9939/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000009939.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture9939.conjecture9939_false`, `Conjecture9939.bound_fails_every_count`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000009939 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
