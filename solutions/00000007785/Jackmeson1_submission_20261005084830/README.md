# Disprove conjecture 00000007785: the cube has Mahler product 4^n/n! < 4^n, so the stated symmetric bound and its Hanner equality cases fail for every n ≥ 2

The conjecture states, in both languages, the symmetric bound M(K) ≥ 4ⁿ and says the Hanner polytopes are its equality cases.
- **Witness.** For every n ≥ 2 the cube [−1,1]ⁿ is an origin-symmetric convex body and a Hanner polytope (an iterated product of segments).
- **Mahler product.** Its polar is the cross-polytope; vol(cube) = 2ⁿ and vol(cross-polytope) = 2ⁿ/n! (Mathlib `volume_sum_rpow_le` with p = 1), so M(cube) = 4ⁿ/n! < 4ⁿ.
- **Consequence.** For every n ≥ 2 the bound M(K) ≥ 4ⁿ fails, and some Hanner polytope is not an equality case. Since this holds in all dimensions n ≥ 2, the "finitely many low-dimensional exceptions (n ≤ 3)" hedge does not rescue the statement.
- **Definitions in Lean.** Polar {y : x·y ≤ 1 ∀x ∈ K}, Mahler product, symmetric convex body (compact, convex, nonempty interior, K = −K), and an inductive Hanner class (segment, product, dual).
- **Main theorem.** `C7785.conjecture_7785_symmetric_clause_false`.
- **Scope.** Refutes the literal 4ⁿ statement only. The nonsymmetric and stability clauses are not addressed, and nothing is claimed for the classical constant 4ⁿ/n!.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 156 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7785/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007785.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7785.conjecture_7785_symmetric_clause_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007785 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
