# Disprove conjecture 00000000172: under its stated definition σ = lim σ_n^{1/n} = 1, so the binary-density and irrationality claims fail

- **Definition.** The conjecture defines σ = lim σ_n^{1/n} with σ₁ = 1, σ_n = σ_{n−1} + σ_{⌊n/2⌋} (OEIS A033485), identically in both languages.
- **σ = 1.** For every sequence with this recurrence: σ_n ≥ 1, monotone, σ_n ≤ n·σ_{⌊n/2⌋}, hence σ_n ≤ n^{⌊log₂ n⌋+1}, so 0 ≤ log σ_n / n → 0 and σ_n^{1/n} → 1 (`sigma_eq_one`).
- **Consequences.** σ = 1 is rational, so the irrationality claim fails. Every binary expansion of 1 is 1.000… or 0.111…, so the count of 1's among the first n digits is 0 or n; for any offset c, c + count is not Θ(log log n), and the density converges (to 0 or 1), so it neither lacks a limit nor tends to +∞.
- **Note.** The usual "Somos' constant" ≈ 1.6617 is a different number and is not addressed; the disproof uses the text's explicit definition.
- **Main theorem.** `C172.conjecture_172_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 256 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture172/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000172.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C172.conjecture_172_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000172 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
