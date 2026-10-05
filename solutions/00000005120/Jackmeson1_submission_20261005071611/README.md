# Prove conjecture 00000005120: (1/2)I and the Jordan block J_n(1/2) share their spectrum, but the condition numbers of matrix inversion differ by 4^(n-1)

The conjecture is existential: two matrices with the same spectrum but exponentially different matrix-function condition numbers, realized by an explicit pair of Jordan structures.

**Witnesses (every n ≥ 2).** `A_n = (1/2) I` (n Jordan blocks of size 1) and `B_n = J_n(1/2)` (one Jordan block of size n).

**Reading (stated in the report).** The matrix function is `f(X) = X⁻¹`. The absolute condition number is the operator norm of the Fréchet derivative, `‖fderiv ℝ f X‖`. The relative one is `cond(f,X)‖X‖/‖f X‖`. Matrices carry the ∞-operator norm (Mathlib `Matrix.linftyOpNormedRing`). "Exponentially different" means a ratio that grows exponentially in the dimension n.

**Proved in Lean** (`Conjecture5120.conjecture_5120`, Mathlib v4.33.1):
- same characteristic polynomial `(X - 1/2)^n`, and both spectra equal `{1/2}`;
- `A_n` and `B_n` are not similar;
- `cond(inv, A_n) = 4` but `cond(inv, B_n) ≥ 4^n`, a ratio of at least `4^(n-1)`;
- relative condition numbers: `1` versus at least `2^n/4`.

The key steps are the explicit inverse `(J_n(1/2)⁻¹)_{ij} = (-1)^(j-i) 2^(j-i+1)` and Mathlib's `fderiv_inverse` (`L(X)Z = -X⁻¹ZX⁻¹`) applied to `Z = E_{n-1,0}`. Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Scope.** The proof covers only `f(x) = 1/x`. For `f = exp` the same pair is not exponentially separated, and the report says so.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture5120/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000005120.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture5120.conjecture_5120`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000005120 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
