# Disprove conjecture 00000008330: (1,2) and (−2,−1) are not gaps of C − C, because C − C lies in [−1,1]

- **Objects.** C = the middle-thirds Cantor set (Mathlib `cantorSet`); C − C = {x − y : x, y ∈ C}.
- **Key fact.** C ⊆ [0,1] and 0, 1 ∈ C, so C − C ⊆ [−1,1] and ±1 ∈ C − C; hence (1, ∞) and (−∞, −1) lie in the complement of C − C.
- **The double gap law fails under four readings.** (R1) The complement is not (−2,−1) ∪ (1,2) (3 is in it). (R2) (1,2) and (−2,−1) are not connected components of the complement, so they are not gaps. (R3) Inside [−2,2], the component through any point of (1,2) contains 2. (R4) (1,2) is not inside the hull [inf, sup] = [−1,1].
- **Scope.** The conjecture is a conjunction, so it is false; the dimension-sum and Newhouse clauses are not assessed.
- **Main theorem.** `C8330.double_gap_law_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 143 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture8330/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000008330.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C8330.double_gap_law_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000008330 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
