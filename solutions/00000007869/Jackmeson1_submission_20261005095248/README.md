# Disprove conjecture 00000007869: the random-order lower bound for every deterministic algorithm contradicts the 3/2 + O(n^{-1/2}) bound for Best Fit

The first two clauses contradict each other. Simple-Best-Fit is itself a deterministic online algorithm, so clause 1 gives R_ro^n(BF) ≥ 3/2 + ε₀ for a fixed constant ε₀ > 0, while clause 2 gives R_ro^n(BF) ≤ 3/2 + C/√n, which is smaller than 3/2 + ε₀ once n > (max(C,0)/ε₀)².
- **Generality.** `clauses_inconsistent` proves the clash for an arbitrary ratio function R and any member A₀ of the algorithm class, so neither the definition of R_ro^n nor the nonstandard name "Simple-Best-Fit" matters.
- **Concrete objects.** Deterministic online bin-packing algorithms, Best Fit (fullest bin that fits), OPT, and R_ro^n = sup over n-item instances of E_σ[A(I_σ)]/OPT(I).
- **Readings refuted.** Clause 1 for all n ≥ 1, eventually, infinitely often, as a limit or as a limsup, against clause 2 eventually; and clause 1 for all n, eventually or as a limit, against clause 2 infinitely often.
- **Not refuted.** Clause 1 "for some n"; both clauses only "infinitely often"; ε₀ depending on n (the Chinese text calls it a constant). The 4/3 → 3/2 clause is not formalized.
- **Main theorem.** `C7869.conjecture_7869_false : ¬ (Clause1 ∧ Clause2)`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 192 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7869/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007869.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7869.conjecture_7869_false`, `C7869.conjecture_7869_false_forall`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007869 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
