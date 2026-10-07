# Disprove conjecture 00000008189: a Poisson(1/2) irregularity index forces density 1−(13/8)e^{−1/2} for index ≥ 3, not e^{−1/2}(1/2)³/3!

The clauses contradict each other. If, for every k, the primes of irregularity index k have relative density e^{−1/2}(1/2)^k/k!, then finite additivity forces density(index ≥ 3) = 1 − (13/8)e^{−1/2} ≈ 0.01439. The statement gives e^{−1/2}(1/2)³/3! ≈ 0.01264 for "at least 3" (≥ 3 in Chinese). Equality would need e^{1/2} = 79/48, i.e. e = 6241/2304 < 2.71, which is false.
- **Definitions.** The irregularity index is the number of even k with 2 ≤ k ≤ p−3 and p | num(B_k), using Mathlib `bernoulli`. Densities are relative natural densities among the primes; Poisson(1/2) is Mathlib's `poissonMeasure`.
- **Generality.** The proof uses only additivity, so the contradiction holds for any finitely additive normalized density.
- **Main theorems.** `C8189.halfPoisson_contradicts_largeIndex : ¬ (HalfPoissonLaw ∧ LargeIndexClause)`, `C8189.conjecture_8189_false`.
- **Scope.** Under an "exactly 3" reading the clauses are consistent and nothing is refuted. The "0.00 expected counterexamples" clause is not formalized.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 119 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture8189/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000008189.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C8189.halfPoisson_contradicts_largeIndex`, `C8189.conjecture_8189_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000008189 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
