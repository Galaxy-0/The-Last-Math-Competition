# Disprove conjecture 00000007794: Reeve tetrahedra break L(P,k)² ≥ L(P,k−1)L(P,k+1)(1+c/k²) for every c > −1

The first clause asks for a universal `c` with `L(P,k)² ≥ L(P,k−1) L(P,k+1) (1 + c/k²)` for all lattice polytopes `P` and all `k ≥ 1`, where `L(P,k) = #(kP ∩ ℤ^d)`.
- **Witness.** Reeve tetrahedra `T_r = conv{(0,0,0),(1,0,0),(0,1,0),(1,1,r)}`: `L(T_r,0) = 1`; `L(T_r,1) ≤ 4` (only the vertices); `L(T_r,2) ≥ r + 1` (the points `(1,1,z)`, `0 ≤ z ≤ r`).
- **Failure.** At `k = 1` the inequality reads `L(1)² ≥ L(2)(1 + c)`, i.e. `16 ≥ (r+1)(1+c)` at best, which fails for large `r` whenever `c > −1`. `T_16` already violates plain log-concavity.
- **Main theorem.** `C7794.conjecture_7794_false`, using Mathlib's `convexHull`, the dilation `(k:ℝ) • P` and `Set.ncard`, with finiteness of the lattice points proved; `L(P,0) = 1` is computed, not assumed.
- **Scope.** Not refuted: `c ≤ −1` (not a margin), a range that excludes `k = 1`, and the simplex-equality and `h*`-annulus clauses; refuting the first clause refutes the conjunction.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 251 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7794/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007794.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7794.conjecture_7794_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007794 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
