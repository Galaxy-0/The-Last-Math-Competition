# Disprove conjecture 00000000751: over ℚ_p, "Julia set nonempty iff degree ≥ 2" fails in both directions

- **Setting.** ℙ¹(ℚ_p) with the chordal metric ρ(z,w) = |z−w|/(max(1,|z|)·max(1,|w|)) (Benedetto–Lee, arXiv:2102.05841, retrieved and quoted), built in Lean as a metric space (triangle inequality proved), with the action of Mathlib's `RatFunc` and degree max(deg num, deg den).
- **Degree 1, nonempty Julia set.** z ↦ z/p has 0 in its Julia set: 0 is a repelling fixed point (|1/p|_p = p > 1), and the points pⁿ → 0 have n-th iterates equal to 1, so the iterates are not equicontinuous at 0. This is the robust core.
- **Degree 2, empty Julia set.** z ↦ z² never increases chordal distance and has no repelling periodic point.
- **Readings.** Three Julia sets are formalized: the complement of the equicontinuity Fatou set, the pointwise non-equicontinuity set, and the closure of the repelling periodic points (any period). The conjecture fails under each, for every prime p, and also over ℂ_p.
- **Not covered.** The Berkovich line (there z² is not a counterexample; the degree-1 direction is unaffected); the "Fatou set open and completely invariant" clause is not examined. Definitions and quotes reused from our package for 00000000745.
- **Main theorems.** `C751.conjecture751_false`, `C751.conjecture751_false_Cp`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 440 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture751/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000751.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C751.conjecture751_false`, `C751.conjecture751_false_Cp`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000751 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
