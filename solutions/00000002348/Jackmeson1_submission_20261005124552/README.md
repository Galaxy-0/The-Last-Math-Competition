# Disprove conjecture 00000002348: an expected condition number is at least 1, never m^{-1/2}

Every condition number satisfies κ(A) ≥ 1: in a nontrivial normed ring ‖1‖ ≥ 1, so 1 ≤ ‖A A⁻¹‖ ≤ ‖A‖‖A⁻¹‖, and σ_min ≤ σ_max. Hence for any random matrix on any probability space, E[κ] ≥ 1 > m^{-1/2} for every sample count m ≥ 2.
- **Definitions.** The condition number on real matrices is defined two ways: ‖A‖‖A⁻¹‖ with the spectral norm (`Matrix.Norms.L2Operator`), and σ_max/σ_min for rectangular matrices; both are +∞ when the matrix is singular. The expectation is the Lebesgue integral over an arbitrary probability space, and matrix sizes may depend on m.
- **Exact reading.** `conjecture_2348_false_exact(_sv)`: E[κ] ≥ 1 and E[κ] ≠ m^{-1/2} for all m ≥ 2.
- **Order readings.** `conjecture_2348_false_order(_sv)`: no real C gives E[κ_m] ≤ C·m^{-1/2} for all large m, which also refutes the proportional, Θ, O and asymptotic readings.
- **Real-valued version.** `one_le_integral_condNum` (Bochner expectation).
- **Not refuted.** m = 1 (where m^{-1/2} = 1 can occur), and non-literal rewordings that change the quantity ("E[κ] − 1 is of order m^{-1/2}", "E[log κ] = m^{-1/2}").
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 226 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #241 by orionsheep was closed without merging. The reviewer did not dispute the argument (κ ≥ 1, so E[κ] ≥ 1 > m^{-1/2}) but rejected the formalization: "conjecture_refuted is (1:Nat) < 2 ∧ 2 ≠ 1; the condition-number bound κ ≥ 1 that constitutes the entire refutation of E[κ] = m^(−1/2) appears only in prose, with no matrices or expectations in Lean." That PR also refuted only the exact value. This submission defines the condition number on actual real matrices in Lean in two ways, both with κ = +∞ for singular matrices. The first is `condNum A = ‖A‖‖A⁻¹‖` for any submultiplicative norm, instantiated with the spectral norm. The second is `svCond A = σ_max/σ_min` for rectangular matrices. It proves κ ≥ 1 from submultiplicativity and from σ_min ≤ σ_max, and it formalizes the expectation as the Lebesgue integral `∫⁻` of a random matrix over an arbitrary probability space. The main theorems `conjecture_2348_false_exact(_sv)` show E[κ] ≥ 1 > m^{-1/2}, so E[κ] ≠ m^{-1/2}, for every m ≥ 2. `conjecture_2348_false_order(_sv)` show that, for every m-indexed family with sizes depending on m, no constant C gives E[κ_m] ≤ C·m^{-1/2} for all large m.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2348/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002348.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2348.conjecture_2348_false_exact`, `C2348.conjecture_2348_false_order`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002348 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
