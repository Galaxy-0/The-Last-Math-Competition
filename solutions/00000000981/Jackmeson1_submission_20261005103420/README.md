# Disprove conjecture 00000000981: no compact operator has point spectrum dense in the unit disk

- **Key lemma.** A compact operator on any complex normed space has only finitely many eigenvalues with |μ| ≥ δ, for each δ > 0 (`finite_eigenvalues_ge`). It is proved here from Mathlib's Riesz lemma and the linear independence of eigenvectors, since Mathlib does not contain it.
- **Consequence.** The open annulus 1/2 < |μ| < 1 contains a point with a neighbourhood free of eigenvalues, so σ_p(T) is not dense in the unit disk (open or closed).
- **Result.** No compact T satisfies the conjecture, however the invariant-subspace clause is read; that clause is formalized but never used.
- **Generality.** Covers compact linear maps and bounded operators (`conjecture_false_clm`) on any complex normed space, in particular Banach and Hilbert spaces.
- **Main theorems.** `C981.conjecture_false`, `C981.conjecture_false_clm`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 166 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture981/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000981.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C981.conjecture_false`, `C981.conjecture_false_clm`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000981 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
