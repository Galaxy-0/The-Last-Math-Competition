# Disprove conjecture 00000001937: the subgroup zeta function of the arithmetic group U(ℤ) ≅ ℤ has abscissa 1, not dim/(dim+1)

- **Witness.** U(ℤ) = {[[1,n],[0,1]] : n ∈ ℤ} = GL₂(ℤ) ∩ U₂(ℚ), the integer points of the 1-dimensional unipotent group U₂ ≅ 𝔾_a; it is constructed in Lean as a subgroup of SL₂(ℤ) (`mem_U_iff`) and is arithmetic under the standard definition (retrieved, quote-checked).
- **Lean objects.** a_n(G), the number of subgroups of index n, for any group (Mathlib `Subgroup.index`, `Nat.card`); the subgroup zeta function as a Mathlib `LSeries`; two abscissae (Mathlib's `abscissaOfAbsConv`, and convergence of the ordered partial sums at real σ).
- **Proved.** a_n(U(ℤ)) = 1 for every n (`subgroupCount_U`), ζ_{U(ℤ)} = riemannZeta on Re s > 1, and both abscissae equal 1 (`subgroupZetaAbscissa_U`, `subgroupZetaAbscissaAbs_U`).
- **Conclusion.** 1 ≠ d/(d+1) for every natural number d (`formula_ne_one`), in particular 1 ≠ 1/2, the predicted value for dim U₂ = 1.
- **Not covered.** The reading that restricts "arithmetic group" to arithmetic subgroups of semisimple groups; conditional convergence at non-real s.
- **Main theorem.** `C1937.conjecture_1937_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 206 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #264 by orionsheep was closed without merging. It used the same counterexample (G = ℤ, whose subgroups of finite index are the nℤ, so ζ_ℤ is the Riemann zeta function with abscissa 1 ≠ 1/2). The reviewer rejected it because "The theorem proves 1 ≠ 2 ∧ 25 > 24 ∧ 2 = 2·1; the entire G = ℤ counterexample (subgroups nℤ, ζ_ℤ = Riemann zeta with abscissa 1 ≠ 1/2) lives in prose with '1 ≠ 2' the only Lean trace. Nothing about Dirichlet series or subgroup zeta functions is formalized." This submission defines in Lean the subgroup counts a_n(G) of an arbitrary group (Mathlib's `Subgroup.index`, with `Nat.card`), the subgroup zeta function as a Mathlib `LSeries`, and two abscissae: Mathlib's `abscissaOfAbsConv`, and the infimum of the real σ at which the ordered partial sums converge. It builds the arithmetic group U(ℤ) = {[[1,n],[0,1]]} ≤ SL₂(ℤ) of the unipotent group U₂ ≅ 𝔾_a and proves that it has exactly one subgroup of each index, that its zeta function is riemannZeta on Re s > 1, and that both abscissae equal 1, which differs from d/(d+1) for every natural number d.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1937/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001937.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1937.conjecture_1937_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001937 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
