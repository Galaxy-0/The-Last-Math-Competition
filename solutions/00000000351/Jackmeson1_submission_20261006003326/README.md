# Disprove conjecture 00000000351: D₃ is not covering-optimal (the body-centred cubic lattice is thinner)

- **Claim refuted.** D_n gives the thinnest lattice covering for every n ≤ 8 (the statement names D_n itself, not its dual). It fails at n = 3, so the conjunction is false.
- **Definitions.** Covering radius μ(L) = the smallest r ≥ 0 such that closed r-balls around L cover ℝⁿ; covering density Θ(L) = vol B(0, μ(L)) / covol(L) (Schürmann–Vallentin, arXiv:math/0403272, retrieved and quoted). "D₃ covering-optimal" = some scaled and rotated copy c·φ(D₃) minimizes Θ among all lattices.
- **D₃ copies.** Every similar copy c·φ(D₃) has the deep hole c·φ(1,0,0), so μ ≥ |c|; its covolume is 2|c|³, so Θ ≥ 2π/3.
- **bcc.** bcc = ℤ³ ∪ (ℤ³ + (½,½,½)) has covolume ½; coordinate rounding to ℤ³ or ℤ³ + h (an averaging argument) gives μ ≤ 5/8, so Θ(bcc) ≤ 125π/192 < 128π/192 = 2π/3 (`coveringDensity_bcc_lt_similar_D3`).
- **Not addressed.** The convention reserving type D_n for n ≥ 4 (no counterexample in 4 ≤ n ≤ 8 is supplied), the dual family D_n* (D₃* = bcc is optimal), the packing–covering ratio, and the clauses about dimension 9 and E₈. Lattice set-up adapted from our accepted package for 00000000238.
- **Main theorem.** `C351.conjecture_351_false` (¬ ∀ n ∈ [3, 8], DCoveringOptimal n).
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 354 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture351/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000351.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C351.conjecture_351_false`, `C351.coveringDensity_bcc_lt_similar_D3`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-06): no solution folder for 00000000351 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
