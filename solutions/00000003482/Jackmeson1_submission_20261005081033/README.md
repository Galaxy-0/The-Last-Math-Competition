# Disprove conjecture 00000003482: the maximal gap χ − χ_f reaches n/10 along n = 5t, so it is not of order n/(log n)²

The order clause ("the maximal order of deviation is n over the logarithm squared") is false.
- **Witness.** The join of t copies of C₅ (n = 5t vertices), built on `Fin (t*5)`.
- **χ ≥ 3t.** Each copy needs 3 colours, and different copies use disjoint colour sets because every cross edge is present.
- **χ_f ≤ 5t/2.** Weight 1/2 on the 5t independent pairs {(i,a),(i,a+2)}. χ_f is the standard LP: the infimum of the total weight of nonnegative weightings of independent sets covering every vertex with weight ≥ 1; the feasible set is proved nonempty.
- **Consequence.** M(5t) ≥ t/2 = n/10, where M(n) is the maximum of χ − χ_f over n-vertex graphs. So M is not O(n/(log n)²), not Θ(n/(log n)²) and not asymptotic to n/(log n)²; more generally it is not O(f) for any f = o(n). (A full M(n) = Θ(n) statement would also need padding by isolated vertices for n not divisible by 5 and the trivial bound χ ≤ n; it is not claimed or needed.)
- **Main theorems.** `maxGap_not_isBigO`, `maxGap_not_isTheta`, `maxGap_not_isEquivalent`, `not_isBigO_of_isLittleO`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 262 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3482/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003482.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3482.maxGap_not_isBigO`, `C3482.maxGap_not_isTheta`, `C3482.maxGap_not_isEquivalent`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003482 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
