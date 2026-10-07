# Prove conjecture 00000001012: the subdegrees of PSL(n,q) on PG(n−1,q) are 1 and (qⁿ − q)/(q − 1)

- **Result.** For every finite field F with q elements, every n ≥ 2 and every point p of PG(n−1,q), the stabilizer of p in PSL(n,q) has exactly two orbits, {p} and the set of all other points, of sizes 1 and (qⁿ − q)/(q − 1).
- **Arithmetic.** The division is exact, and (qⁿ − q)/(q − 1) = (qⁿ − 1)/(q − 1) − 1 ≥ 2; so the set of subdegrees is exactly {1, (qⁿ − q)/(q − 1)}, and the action is transitive and faithful.
- **Group and space.** Mathlib's PSL = SL/Z(SL) (`Matrix.ProjectiveSpecialLinearGroup`) acting on `Projectivization F (Fin n → F)` through SL.
- **Key input.** Mathlib's 2-transitivity of SL on projective space (Projectivization/Action.lean), passed to PSL; the point count from `Projectivization.card`. n ≥ 2 is needed: PG(0,q) is a single point (`card_points_one`).
- **Reading.** "Of the (qⁿ − q)/(q − 1) type" is read as "the subdegrees are 1 and (qⁿ − q)/(q − 1)"; the strawman reading that the trivial subdegree 1 also equals the formula (false for any transitive action on more than one point) is rejected. The "minimal degree" phrase of the Definition line is not formalized.
- **Main theorem.** `Conjecture1012.subdegrees_PSL`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 212 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1012/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001012.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture1012.subdegrees_PSL`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001012 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
