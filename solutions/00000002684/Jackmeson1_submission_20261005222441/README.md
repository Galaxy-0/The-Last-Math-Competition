# Disprove conjecture 00000002684: orbit–subvariety hit counts can grow like n/2, beating every polynomial in log n

- **Witness (every r ≥ 1).** f(x₁,…,x_r,z) = (−x₁, x₂,…,x_r, z+1) on 𝔸^{r+1}_ℚ, x₀ = (1,0,…,0;0), V = {x₁ = 1, x₂ = … = x_r = 0}: the zero locus of r degree-1 equations with a prime vanishing ideal and a coordinate ring of Krull dimension 1, inside an ambient space of Krull dimension r+1 — an irreducible subvariety of codimension r.
- **Count.** fⁿ(x₀) ∈ V exactly for even n, and the orbit is injective, so #(orbit ∩ V up to N) ≥ N/2.
- **Refutation.** Since P(log N) = o(N), for every real polynomial P the count is not eventually ≤ P(log N); this refutes the degree-r upper-bound reading and the equality reading, whatever the coefficients.
- **Finite intersections.** g_K(x,z) = (∏_{j<K−1}(z − j), x₂,…,x_r, z+1) from 0 meets the z-axis in exactly K points: if the count eventually equals P(log N) then P is constant (so not of degree r ≥ 1), and no single P with coefficients depending only on the subvariety bounds the count for all K.
- **Not refuted.** Finite intersections with coefficients allowed to depend on (f, x₀), where the upper bound is trivially true; the Definition line's "finiteness of intersections" framing is discussed in proof.tex.
- **Main theorem.** `Conjecture2684.conjecture2684_disproof`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 461 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2684/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002684.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture2684.conjecture2684_disproof`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002684 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
