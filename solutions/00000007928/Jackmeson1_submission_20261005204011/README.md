# Disprove conjecture 00000007928: |K₂(O_F)| = |ζ_F(−1)|·D_F·2^{[F:ℚ]} fails for F = ℚ

- **Claim refuted.** The displayed formula w₂(F) = |K₂(O_F)| = |ζ_F(−1)|·D_F·2^{[F:ℚ]} (stated in both languages); refuting it refutes the conjunction.
- **Witness F = ℚ.** ζ_ℚ is the Riemann zeta function, ζ(−1) = −B₂/2 = −1/12, d_ℚ = 1, [ℚ:ℚ] = 1, so the right side is 1/6, which is not an integer and hence not the order of any group — whatever K₂(ℤ) is. Lean quantifies over every type G via `Nat.card`.
- **Zeta in Lean.** Mathlib's `NumberField.dedekindZeta` is the raw L-series (junk at s = −1), so it is never evaluated there: each ideal count aₙ = 1 for O_ℚ ≅ ℤ, so it equals `riemannZeta` on Re s > 1, and by the identity theorem on ℂ∖{1} every holomorphic continuation takes the value −1/12 at −1; `riemannZeta_is_continuation` shows the hypotheses are satisfiable.
- **Sources.** Wikipedia "Dedekind zeta function" and "Birch–Tate conjecture" (retrieved, quotes checked); the parenthetical "integralization of a rational identity" is addressed in proof.tex — the main clause asserts an equality of orders and names no integralization procedure.
- **Not addressed.** The dilogarithm p-part and unit-rank clauses; readings restricted to fields of positive unit rank or to an unspecified integralization. K₂ itself is not built (the argument does not depend on it).
- **Main theorems.** `C7928.conjecture_7928_false`, with corollaries `conjecture_7928_false_riemannZeta` and `conjecture_7928_false_finite_group`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 141 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7928/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007928.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7928.conjecture_7928_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007928 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
