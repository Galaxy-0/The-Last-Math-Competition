# Disprove conjecture 00000000982: Berezin fixed points on the Fock space are neither all radial nor at most two

- **Definition.** The Berezin transform is (Bf)(z) = ∫ f(w)|k_z(w)|² dλ(w), with k_z(w) = e^{w z̄ − |z|²/2} and dλ = π⁻¹e^{−|w|²} dA, i.e. the textbook ⟨T_f k_z, k_z⟩. Lean proves that k_z is the reproducing kernel e^{w z̄} normalized by e^{|z|²/2}.
- **Gaussian convolution.** B is a Gaussian convolution (`berezin_eq_conv`, from Mathlib's `GaussianFourier.integral_rexp_neg_mul_sq_norm`); the first moment vanishes by rotating the plane (`moment_zero`).
- **Fixed points.** Constants and every monomial z^k are fixed (`berezin_const`, `berezin_pow`). z lies in the Fock space and is not radial, so the radial clause fails.
- **Cardinality.** The fixed-point set is infinite, both in the Fock space and among bounded symbols (all constants), so the "at most 2" clause fails; the monomials are linearly independent, so a dimension reading also fails in the Fock space.
- **Not refuted.** If symbols are bounded and "cardinality" means dimension, the statement holds (the bounded fixed points are the constants).
- **Main theorem.** `C982.conjecture_982_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 231 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** A submission by earthking11 for this conjecture was merged and then removed in the full re-audit (commit 541cf4fb). The re-audit's reason: "no Berezin/Fock objects; load-bearing theorem prose-only". Its Lean (`import Std` only) modelled z on the integer lattice. It proved only that (1,0) and (0,1) are distinct and that 1, z, z^2 are distinct functions; the convolution identity B = e^{Delta/4} and the fact that B fixes z appeared only in prose. This submission defines in Lean the Fock space F^2 (entire functions square-integrable against pi^{-1} e^{-|w|^2} dA), its normalized reproducing kernel, and the Berezin transform as an actual Lebesgue integral over C. It proves the Gaussian convolution form, B(c) = c and B(w^k) = w^k from Mathlib's Gaussian integral, F^2 membership, that w -> w is not radial, that the monomials are linearly independent, and that the fixed-point set is infinite both in F^2 and among bounded symbols.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture982/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000982.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C982.conjecture_982_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000982 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
