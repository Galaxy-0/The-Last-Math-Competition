# Disprove conjecture 00000008197: genus-2 semigroups refute the genus-3 symmetry breaking and the 1-2^{-g} concentration

The conjecture is a conjunction of five clauses about the distribution wgap(g) of Weierstrass gap semigroups, the numerical semigroups of genus g. One clause says the minimal genus of symmetry breaking (nonsymmetric semigroups) is g = 3. Another says the symmetric semigroups have share 1 - 2^{-g}.

**Third-genus breaking fails.**
- <3,4,5> = N \ {1,2} is a numerical semigroup of genus 2 with Frobenius number 2.
- It is not symmetric: the gap 1 also has F - 1 = 1 as a gap, or equivalently g = 2 != (F+1)/2.
- Every semigroup of genus 0 or 1 is symmetric, so the least genus of a nonsymmetric numerical semigroup is exactly 2.
- <3,4,5> occurs on curves: it is the semigroup at every non-Weierstrass point of every genus-2 curve.

**Weierstrass-point-only reading.** Suppose only Weierstrass points proper (non-ordinary semigroups) count. Every genus-2 numerical semigroup has gaps {1,2} or {1,3}, so the only non-ordinary one is the symmetric <2,5>. Every probability distribution on these semigroups therefore gives the symmetric ones mass 1, not 1 - 2^{-2} = 3/4, so the concentration formula fails at g = 2.

**Lean.** `Conjecture8197.conjecture_00000008197_false (P Q : Prop)` proves:
- `¬(ThirdGenusBreaking ∧ P)` and `¬(ConcentrationFormula 2 ∧ Q)`;
- `IsLeast nonsymmetricGenera 2`;
- that every PMF on `WeierstrassType 2` gives mass 1 to the symmetric semigroups.

Numerical semigroups are `AddSubmonoid ℕ` with finite complement; symmetry follows Rosales and Garcia-Sanchez. The only axioms used are propext, Classical.choice and Quot.sound.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture8197/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000008197.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture8197.conjecture_00000008197_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000008197 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
