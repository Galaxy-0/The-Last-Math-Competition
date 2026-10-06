# Disprove conjecture 00000009984: squared irreducible dimensions of a semisimple Hopf algebra need not divide its dimension

The conjecture asserts, with an empty exception list, that for every finite-dimensional semisimple Hopf algebra A each squared irreducible dimension (dim M)² divides dim A.
- **Counterexample.** The group algebra ℂ[S₃] with Mathlib's Hopf structure (Δg = g ⊗ g, ε g = 1, S g = g⁻¹): dimension 6, semisimple by Maschke, group-like coalgebra. Its irreducible dimensions are 1, 1, 2, and 2² = 4 does not divide 6.
- **Lean argument.** If every simple module had (dim)² | 6, all would be 1-dimensional; commutators would then annihilate every simple left ideal, hence all of ℂ[S₃] (a sum of its simple left ideals), making it commutative. But (01)(12) ≠ (12)(01).
- **Main theorem.** `C9984.disproof`: not every finite-dimensional semisimple Hopf algebra over ℂ satisfies the clause (`SquaredDimsDivide`: every finite-dimensional simple module M has (finrank M)² | finrank A).
- **Scope.** Only the divisibility clause, read literally as dᵢ² | dim A, is refuted; the reading dᵢ | dim A (Kaplansky's divisibility) is not addressed.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 127 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture9984/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000009984.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C9984.disproof`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000009984 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
