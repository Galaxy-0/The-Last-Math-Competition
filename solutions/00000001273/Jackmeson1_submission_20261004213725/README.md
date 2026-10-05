# Disprove conjecture 00000001273: periodic points of a mixing Z^2 SFT without the claimed main term

The conjecture says that every mixing SFT under a ℤ² action has a periodic-point count with main term `λ^{t₁t₂}·(1 + O(2^{-min t}))`.

**Counterexample.** Let `X = {x ∈ {0,1,2}^{ℤ²} : x(i,j) ≠ x(i+1,j)}`: each row is a proper 3-colouring, and there is no vertical constraint.
- `X` is a nonempty SFT, defined by three forbidden horizontal dominoes.
- `X` is mixing, in the standard cylinder sense; a gluing construction proves it.
- `X` has `P(t₁,t₂) = (2^{t₁} + 2(-1)^{t₁})^{t₂}` points of period `(t₁,t₂)`. This uses a bijection with families of cycle colourings and a transfer-matrix induction.

**Contradiction.** Suppose `λ, C, T` existed. Fix a large even `t₁ = 2k` and let `t₂ → ∞`; this forces `λ^{2k} = 2^{2k} + 2` for every large `k`, and three consecutive values of `k` are incompatible.

Lean refutes two readings, each with violations past every threshold (an infinite family of counterexamples, not finitely many cases):
- the explicit error-term reading;
- the weaker reading where the ratio only tends to 1.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1273/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001273.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture1273.conjecture_00000001273_false`, `Conjecture1273.conjecture_00000001273_mainTerm_false`, `Conjecture1273.conjecture_00000001273_disproved`, `Conjecture1273.X3_counterexample`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000001273 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
