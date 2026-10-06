# Disprove conjecture 00000009994: the finitistic dimension is not bounded by twice (or any function of) the Loewy length

- **Claim refuted.** findim(A) ≤ 2·LL(A) for finite-dimensional algebras, with a bound independent of quiver size (first clause), over every field k; this refutes the conjunction (the optimality / exterior-algebra clauses are not addressed).
- **Witness.** Λ_{m+1}, the radical-square-zero algebra of the linear quiver with m+1 vertices, built as `TrivSqZeroExt (k^{m+1}) (k^m)` with the twisted arrow bimodule (the name kA_n/J² is descriptive; any finite-dimensional algebra is a valid witness).
- **Loewy length.** J(Λ) is the arrow ideal, J² = 0 and J ≠ 0, so LL = 2 (`mem_jacobson_iff`, `loewyLength_eq_two`); LL = the smallest positive L with J^L = 0 (arXiv:1912.09044, retrieved).
- **Projective dimension.** S₀ and P_{i+1} = Λe_{i+1} are projective retracts of Λ; the sequences 0 → S_i → P_{i+1} → S_{i+1} → 0 are short exact with S_{i+1} not projective, so Mathlib's `hasProjectiveDimensionLT_X₃_iff` and induction give pd S_j = j.
- **Refutation.** S_m is one-dimensional with pd m < ∞, so findim(Λ_{m+1}) ≥ m; with 6 vertices findim ≥ 5 > 4 = 2·LL (`headline`), and m = f(2) + 1 refutes every bound f(LL) (`family`).
- **Definitions.** findim = the standard little finitistic dimension (sup of Mathlib's `projectiveDimension` over finite-dimensional modules of finite projective dimension; arXiv:2412.10965, retrieved); the literal Definition line (without "finite pd") is refuted too.
- **Main theorem.** `Conjecture9994.conjecture_9994_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 551 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture9994/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000009994.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture9994.conjecture_9994_false`, `Conjecture9994.headline`, `Conjecture9994.family`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-06): no solution folder for 00000009994 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
