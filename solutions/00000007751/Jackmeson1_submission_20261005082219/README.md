# Disprove conjecture 00000007751: a degree-2 rational map over Q has 12 rational preperiodic points, so MSD(1,2) ≠ 9

The conjecture claims that the least uniform bound MSD(1,2) on the number of Q-rational preperiodic points of degree-2 rational maps P¹ → P¹ over Q is 9.
- **Witness.** f(z) = (−2z²−3z−1)/(2z²−z). Numerator and denominator are coprime (Bezout: (4X−3)P + (4X+5)Q = 3) and both have degree 2.
- **Preperiodic points.** P¹(Q) contains two 3-cycles, ∞ → −1 → 0 → ∞ and −5/2 → −2/5 → −1/6 → −5/2, plus the tails −1/2, 1/2, −1/4, −3/2, −1/3, 2: 12 preperiodic points in all (11 finite). So MSD(1,2) ≥ 12.
- **Model.** P¹(Q) = `Option ℚ`, with the map given by the homogeneous formula (`act_wellDefined`). Preperiodic means the forward orbit is finite. The 12 points are an explicit Finset closed under f; the count is proved, not hardcoded.
- **Main theorems.** `C7751.MSD_ne_nine : MSD 2 ≠ 9`, plus `twelve_le_MSD`, `not_all_le_nine`, `exists_degree_two_eleven_affine_preperiodic`.
- **Scope.** The text says "rational map", not polynomial (Poonen's bound 9 is for quadratic polynomials). Not addressed: uniqueness of an extremal map, and the general (d^{2N+2}−1)/(d−1) clause.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 163 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7751/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007751.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7751.MSD_ne_nine`, `C7751.twelve_le_MSD`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007751 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
