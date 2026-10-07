# Disprove conjecture 00000004515: the planar random Euclidean MST has no (log n)^{1/4} factor

- **Strip bound.** Any n ≥ 1 points of [0,1]² have Euclidean MST length ≤ 3√n + 2: the path through the points sorted by strip, then abscissa (k = ⌊√n⌋ + 1 strips), telescopes to this bound. Translating and scaling gives W_n ≤ 2R(3√n + 2) for points in [−R, R]².
- **Expectation.** For iid points with any law concentrated on a bounded set (uniform on the unit square or disk included), 0 ≤ E[W_n] ≤ C(3√n + 2), so E[W_n]/(c√n(log n)^β) → 0 for every real c and every β > 0.
- **Refuted readings.** E[W_n] ~ c√n(log n)^{1/4} (every real c); equality for large n (c > 0); Θ(√n(log n)^{1/4}), i.e. the "exact exponent 1/4"; and E[W_n] ≥ c√n(log n)^{1/4} infinitely often (c > 0).
- **Objects in Lean.** MST length = minimum over trees on Fin n of the summed Euclidean edge lengths (√(Δx² + Δy²), since Mathlib's `dist` on ℝ×ℝ is the sup metric); expectation = integral against the product measure `Measure.pi`, with measurability and integrability proved.
- **Not covered.** The c = 0 equality reading (excluded by "exponent 1/4 exact"), unbounded unit-area regions, power-weighted edge lengths; the "long-edge density formula" clause is read as an explanation of the exponent.
- **Main theorems.** `C4515.conjecture_4515_false` (general bounded law), `C4515.conjecture_4515_false_uniform`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 414 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4515/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004515.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C4515.conjecture_4515_false`, `C4515.conjecture_4515_false_uniform`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004515 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
