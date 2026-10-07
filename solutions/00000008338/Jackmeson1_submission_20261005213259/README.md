# Disprove conjecture 00000008338: the optimal Siegel constant for 1×2 systems is H, not (nH)^{m/(n−m)} = 2H

- **Object.** The Definition line names sieg_c as the height upper bound of minimal solutions: the sup, over integer m×n systems with coefficients not all 0 and bounded by H, of the least sup-norm height of a nonzero integer kernel vector. The conjecture claims sieg_c = (nH)^{m/(n−m)} and that this value is attained.
- **Computation.** At (m,n) = (1,2), every row (a,b) has the kernel vector (b,−a) (or (1,0) when a = b = 0) of height ≤ H; the row (H, H−1) forces x₁ = H(x₀ + x₁), so H | x₁ ≠ 0 and the least kernel height is exactly H. Hence sieg_c(1,2,H) = H for every H ≥ 1, and H is the least real bound (`isLeast_real_bound`).
- **Refutation.** The claimed value is (2H)^{1/(2−1)} = 2H > H; no admissible 1×2 system, random or not, attains it, and the ratio 1/2 rules out asymptotic equality too. This hits the main clause (and the attainment clause), not a parenthetical.
- **Not refuted.** "(nH)^{m/(n−m)} is a valid bound" (Siegel's lemma) and "only the exponent is sharp" (the exponent 1 is sharp here); the tail clauses are not addressed. Per the retrieved Wikipedia passage, (NB)^{M/(N−M)} is Siegel's bound; the formula is tested exactly as written.
- **Main theorems.** `Conjecture8338.conjecture8338_false`, `Conjecture8338.not_siegC_eq_bvValue`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 243 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture8338/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000008338.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture8338.conjecture8338_false`, `Conjecture8338.not_siegC_eq_bvValue`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000008338 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
