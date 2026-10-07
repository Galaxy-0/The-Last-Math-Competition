# Disprove conjecture 00000000745: the Julia set of x² − 1 on ℤ₂ is empty, so its Hausdorff dimension is 0, not 1

- **Map and space as stated.** f(x) = x² − 1 on the 2-adic integers ℤ₂; the chordal metric equals the 2-adic metric there (`chordal_eq_dist`).
- **Equicontinuity.** f(x) − f(y) = (x − y)(x + y) with |x + y|₂ ≤ 1, so every iterate is 1-Lipschitz; the iterates are uniformly equicontinuous and the Fatou set is all of ℤ₂.
- **No repelling points.** By the chain rule in ℚ₂, (fⁿ)'(x) = ∏_{i<n} 2fⁱ(x), so |(fⁿ)'(x)|₂ ≤ 2^{−n} < 1.
- **Four readings.** The non-Fatou set, the points of non-equicontinuity, the repelling periodic points (any period n > 0), and their closure are all empty (`julia_facts`).
- **Refutation.** dim_H J = dim_H ∅ = 0 ≠ 1, while Jᶜ = ℤ₂ is open and dense: the second conjunct holds, the first fails, so the conjunction is false.
- **Definitions (retrieved).** Wikipedia "Arithmetic dynamics" (equicontinuity definition; in the non-archimedean setting the Julia set may be empty), Benedetto–Lee arXiv:2102.05841 (Fatou set via chordal equicontinuity; repelling multiplier), Wikipedia "Julia set" (closure of repelling periodic points).
- **Not addressed.** The Berkovich Julia set; the Julia set on ℙ¹(ℚ₂) or ℙ¹(ℂ₂) intersected with ℤ₂ is covered only by a remark.
- **Main theorem.** `C745.conjecture745_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 183 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture745/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000745.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C745.conjecture745_false`, `C745.julia_facts`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000745 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
