# Disprove conjecture 00000003238: a direct sum of nilpotent Jordan blocks has spectrum the closed unit disc, not the closure of the union of the block spectra

- **Claim refuted.** The spectrum of a direct sum ⊕A_n of a uniformly bounded family of Hilbert-space operators equals the closure of ⋃σ(A_n); the undefined "accumulated edges" clause is not needed.
- **Witness.** A_n = J_n, the nilpotent shift on ℂ^{n+1}, with ‖J_n‖ ≤ 1 and σ(J_n) = {0} (`spectrum_shift`), so the closure of the union is {0}.
- **Direct sum.** T = ⊕J_n on Mathlib's Hilbert sum `lp (fun n => EuclideanSpace ℂ (Fin (n+1))) 2`, shown to act blockwise and to be the unique such bounded operator (`dsum_apply`, `dsum_single`, `dsum_unique`); spectra are Mathlib's `spectrum ℂ` in the Banach algebra of bounded operators.
- **Spectrum of T.** σ(T) = the closed unit disc (`spectrum_T`): for |z| < 1 the vectors (1, z, …, zⁿ) give (z − J_n)v = z^{n+1}e_n with ‖v‖ ≥ 1, so z − T is not bounded below.
- **Not refuted.** Finite direct sums and normal families (where the identity holds); the text assumes neither. Only the Hilbert (ℓ²) direct sum is treated; the family quantified over is contractive and ℕ-indexed.
- **Main theorem.** `C3238.not_edgeTheorem`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 273 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3238/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003238.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3238.not_edgeTheorem`, `C3238.spectrum_T`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-06): no solution folder for 00000003238 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
