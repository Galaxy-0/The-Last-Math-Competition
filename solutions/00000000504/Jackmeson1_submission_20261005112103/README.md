# Disprove conjecture 00000000504: pd R/I(G) is unbounded on r-partite r-uniform hypergraphs, so 2r−1 is not a threshold

- **Claim.** pd R/I(G) has "threshold 2r−1" for r-partite r-uniform hypergraphs (generalizing "pd ≤ 3 for bipartite graphs").
- **Refuted readings.** (A) pd R/I(G) ≤ 2r−1 for all such G; (B) the supremum of pd over the class is 2r−1. Both fail for every field k and every r ≥ 1.
- **Witness.** The r-uniform matching with m disjoint edges. Its edge monomials use disjoint variables, so they form a regular sequence, and pd R/I ≥ m. Taking m = 2r gives pd ≥ 2r > 2r−1 (for r = 2: four disjoint edges have pd ≥ 4 > 3).
- **Lean route.** Monomials in disjoint variables are weakly regular (proved by hand from the monomial-ideal membership criterion). Localize at the ideal of polynomials with zero constant term, apply Mathlib's `projectiveDimension_quotient_eq_length`, and transfer back since localization does not increase pd.
- **Main theorems.** `Conjecture504.conjecture504_upper_bound_false`, `Conjecture504.conjecture504_unbounded`. pd is Mathlib's categorical `projectiveDimension` in `ModuleCat`, valued in `WithBot ℕ∞`; only lower bounds are proved.
- **Scope.** Not addressed: readings of the form "pd ≤ 2r−1 iff (unspecified property)"; the lower-bound reading is not formalized.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 236 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture504/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000504.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture504.conjecture504_upper_bound_false`, `Conjecture504.conjecture504_unbounded`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000504 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
