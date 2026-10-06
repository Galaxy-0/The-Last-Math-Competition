# Prove conjecture 00000003287: Gauss quadrature nodes are the zeros of the orthogonal polynomial, and 2n−1 is the maximal precision

- **Setting.** The classical Gauss–Christoffel theorem for any measure μ on ℝ with finite moments and infinite support; weight functions w(x)dx are a special case (`notFinitelySupported_withDensity`). Known theorem, proved from scratch.
- **Orthogonal polynomials.** The monic orthogonal p_n exists and is unique, and consecutive ones satisfy the three-term recurrence p_{n+2} = (X − a)p_{n+1} − b·p_n with b > 0 (`three_term_recurrence`).
- **Zeros.** p_n has n real roots, all simple: write p_n = P·q with q root-free; q has constant sign by the IVT, and orthogonality rules out p_n·s ≥ 0 for s ≠ 0 of degree < n.
- **Exactness.** The Gauss rule (nodes = zeros of p_n, weights = Christoffel numbers ∫ℓᵢ dμ) has positive weights and is exact up to degree 2n − 1 (divide by p_n with `modByMonic`, interpolate the remainder).
- **Maximality.** No n-node rule with any nodes and weights is exact in degree 2n (∫∏(x − xᵢ)² dμ > 0 while the rule gives 0), so the Gauss rule's `algebraicPrecision` is exactly 2n − 1; every n-node rule exact to degree 2n − 1 has p_n = ∏(X − xᵢ), so its nodes are exactly the zeros of p_n.
- **Scope.** Favard's converse (abstract recurrence families with no weight given) is not formalized; finite moments are a hypothesis; n ≥ 1. Sources: Wikipedia "Gaussian quadrature" and "Orthogonal polynomials" (retrieved, quotes checked).
- **Main theorems.** `C3287.gauss_christoffel`, `C3287.three_term_recurrence`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 429 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3287/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003287.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3287.gauss_christoffel`, `C3287.three_term_recurrence`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003287 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
