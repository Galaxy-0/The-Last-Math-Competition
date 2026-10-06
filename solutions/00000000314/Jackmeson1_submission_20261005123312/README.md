# Disprove conjecture 00000000314: every M(√p) is at least 2√2, so {M(√p)} is not dense in [√5, 3)

- **Readings.** Two readings of M are refuted: the standard Lagrange value M(α) = limsup 1/(q‖qα‖), and the literal printed formula limsup 1/‖qα‖.
- **Pell.** x² − p·y² = 1 has solutions with y arbitrarily large (Mathlib `Pell.IsFundamental`, `y_strictMono`). For each one, ‖y√p‖·2y√p ≤ (x − y√p)(x + y√p) = 1.
- **Bound.** Hence M(√p) ≥ 2√p ≥ 2√2 in the standard reading, and M(√p) = ∞ in the literal one. Since √5 < 2√2 < 3, no M(√p) lies in the open subinterval (√5, 2√2) of [√5, 3).
- **Density.** Both senses fail: [√5,3) ⊆ closure S, and "a value lies between any a < b". The second conjunct ("density follows from transition statistics") presupposes the density and falls with it.
- **Main theorem.** `C314.conjecture314_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 230 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture314/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000314.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C314.conjecture314_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000314 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
