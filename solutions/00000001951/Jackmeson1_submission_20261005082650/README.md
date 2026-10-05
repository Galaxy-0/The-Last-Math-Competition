# Disprove conjecture 00000001951: Out(F_n) has a subgroup of index 2, so the smallest proper index is not 2ⁿ·C(n,2)

The conjecture claims, for n ≥ 3, that Out(F_n) fails CSP and that the smallest index of a proper subgroup of Out(F_n) is 2ⁿ·C(n,2).
- **Determinant character.** [φ] ↦ det(φ_ab), the determinant of the induced map on F_n^ab = ℤⁿ, is a well-defined homomorphism Out(F_n) → {±1}, because inner automorphisms act trivially on ℤⁿ.
- **Surjective.** Inverting one free generator has determinant −1, so the kernel is a proper normal subgroup of index 2.
- **Consequence.** The smallest index of a proper finite-index subgroup is 2 for every n ≥ 1, and 2 < 2ⁿ·C(n,2) for n ≥ 2 (24 at n = 3).
- **Lean model.** Out(F_n) := `MulAut (FreeGroup (Fin n)) ⧸ range MulAut.conj` (normality proved); the abelianization is the explicit exponent-sum map F_n → ℤⁿ.
- **Main theorems.** `C1951.smallest_index_ne : 3 ≤ n → sInf (properIndices n) ≠ 2 ^ n * n.choose 2`, `sInf_properIndices` (= 2 for every n ≥ 1), `exists_normal_index_two`.
- **Scope.** The CSP clause (open for n ≥ 3) is not addressed; the conjunction fails on the index clause.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 195 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1951/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001951.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1951.smallest_index_ne`, `C1951.sInf_properIndices`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001951 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
