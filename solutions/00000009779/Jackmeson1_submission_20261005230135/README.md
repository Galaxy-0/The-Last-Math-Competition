# Disprove conjecture 00000009779: a C^k kernel on [0,1]^d with eigenvalues λ_n ≥ ½ n^{−k−5/4}, so not O(n^{−k−1−d/2})

- **Claim refuted.** Every C^k kernel on a d-dimensional domain has eigenvalues with |λ_n| ≤ C n^{−k−1−d/2} (the exponent as written in both languages).
- **Witness.** For every D ≥ 1 and k ≥ 0, K(x,y) = f(x₀ − y₀) on [0,1]^D with f(t) = Σ_{m≥1} m^{−(k+5/4)} cos(2πmt): real, symmetric, positive semidefinite, and C^k on ℝ^D × ℝ^D (`contDiff_tsum`).
- **Eigenfunctions.** e^{2πimx₀} are orthonormal in L²([0,1]^D) and satisfy T_K φ_m = ½ m^{−(k+5/4)} φ_m pointwise (termwise integration by dominated convergence).
- **Refutation.** For any C and large n, the first n of them have eigenvalues above C n^{−k−1−D/2}, since (k+1+D/2) − (k+5/4) ≥ 1/4; so no C works (`not_eigenBound`), and the optimal-constant clauses presuppose a constant that does not exist. For D = 1 the kernel is radial, f(|x−y|), so the radial clause also has no constant (`main_radial`).
- **Scope.** The step from n orthonormal eigenfunctions to the n-th eigenvalue in decreasing order (with multiplicity) is Lemma 1 of proof.tex (elementary, not formalized). The domain [0,1]^D is our choice (none is named); for D ≥ 2 the kernel depends only on the first coordinate. A different exponent (e.g. −1−k/d, if the stated one is a typo) is not refuted.
- **Main theorems.** `C9779.main`, `C9779.main_radial`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 384 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture9779/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000009779.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C9779.main`, `C9779.main_radial`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000009779 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
