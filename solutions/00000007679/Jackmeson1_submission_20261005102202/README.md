# Disprove conjecture 00000007679: the zero sets of S_N are real, so they converge to no Jordan curve

- **Product formula.** With the Gaussian binomial defined by its textbook formula, the q-Pascal rule gives S_{N+1}(z) = (1 − z qᴺ) S_N(z), so S_N(z) = ∏_{k<N}(1 − z q^k) (Cauchy binomial theorem).
- **Zeros.** The zero set is {q^{−k} : k < N} ⊂ ℝ for every q ∈ (0,1).
- **No Jordan curve.** A Jordan curve cannot lie in ℝ (intermediate value theorem on Re γ over the two half-circles). Hausdorff convergence, and any notion in which every limit point is a limit of zeros, forces the limit into the closure of the union of the zero sets, which lies in ℝ; this holds also after real affine normalisations a_N z + b_N (e.g. z ↦ qᴺz).
- **Quasicircle clause.** A quasicircle is a Jordan curve, so the claimed quasicircle limit does not exist.
- **Main theorem.** `C7679.conjecture_7679_false`.
- **Scope.** Not formalised: Riemann-sphere convergence (argued in prose: the closure there is countable) and non-real complex rescalings.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 226 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7679/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007679.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7679.conjecture_7679_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007679 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
