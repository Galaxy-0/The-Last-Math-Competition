# Prove conjecture 00000007000: a permutation pair preserves the box norm but changes the scattering spectrum

- **Reading:** functions are real functions on a finite grid `X × Y`; the box norm is the Gowers box norm `‖f‖_□ = (E f(x,y) f(x,y') f(x',y) f(x',y'))^{1/4}`; a permutation pair `(σ, τ)` acts by `f ↦ f ∘ (σ × τ)`; on `ZMod 4 × ZMod 4` the scattering spectrum is the diffraction intensity `|f̂(ξ)|²` and the phase is `f̂(ξ)/|f̂(ξ)|`.
- **General lemma:** every permutation pair preserves the box norm (`boxNorm_permute`), by reindexing the four-fold sum.
- **Witnesses:** `f = 1_{x ∈ {0,1}} · 1_{y = 0}`, `σ = (1 2)`, `τ = (0 1)`, `g = f ∘ (σ × τ) = 1_{x ∈ {0,2}} · 1_{y = 1}`.
- **Same norms:** `‖g‖_□ = ‖f‖_□ > 0` (the box-norm sum of `f` is 4).
- **Different scattering spectra:** `f̂(1,0) = 1 - i`, `ĝ(1,0) = 0`, so the intensities are 2 and 0.
- **Different phase:** `f̂(0,1) = 2`, `ĝ(0,1) = -2i`: equal intensity 4, phases `1` and `-i`.
- **Lean** (Mathlib v4.33.1): `conjecture7000 : ∃ f g σ τ, σ ≠ 1 ∧ τ ≠ 1 ∧ g = permute σ τ f ∧ boxNorm g = boxNorm f ∧ 0 < boxNorm f ∧ intensity f ≠ intensity g ∧ … ∧ phase f (0,1) ≠ phase g (0,1)`. The character `i^k` is proved equal to `exp(2πik/4)` (`exp_eq`). Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- **Scope:** Fourier-intensity reading of "scattering spectrum"; the wavelet scattering transform and scattering matrices are not treated.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7000/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007000.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Submission00000007000.conjecture7000`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007000 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
