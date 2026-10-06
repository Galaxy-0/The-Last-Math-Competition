# Disprove conjecture 00000001673: the inducibility of C6 is at most 2/7, not (√3−1)/2

The conjecture claims ind(C₆) = (√3−1)/2 ≈ 0.366, attained by balanced triangular-prism blow-ups.
- **Local bound.** In any graph, at most two one-vertex deletions of a 7-vertex set b induce C₆. C₆ is 2-regular, so two such deleted vertices are twins in the rest of b; a third deletion would put twins inside an induced C₆, which has none.
- **Averaging over 7-sets.** For every n ≥ 7 and every graph on n vertices, the induced C₆ density is ≤ 2/7 < (√3−1)/2. Hence the limit, limsup and liminf of the maximum density, and the limsup along any graph sequence, all differ from (√3−1)/2.
- **Extremal clause.** Every blow-up of the prism K₃ □ K₂ contains no induced C₆ (C₆ is twin-free and triangle-free), while balanced C₆ blow-ups give ind(C₆) ≥ 5/324, so prism blow-ups are not extremal.
- **Definitions.** An induced copy is the image of an induced embedding `cycleGraph 6 ↪g G`; density divides by C(n,6); `indC6` is the limsup of the maximum density over graphs on `Fin n`.
- **Main theorem.** `C1673.not_conjecture`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 308 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1673/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001673.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1673.not_conjecture`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001673 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
