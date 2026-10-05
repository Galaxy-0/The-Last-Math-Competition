# Disprove conjecture 00000003462: K6 breaks the (5v-2)/3 bound and no six-doubly-critical graph attains it

The conjecture says the edge bound for six-doubly-critical graphs improves to `(5v−2)/3`, and that the bound is attained uniquely by Kostochka–Yancey extremal graphs. The English and Chinese versions define the class differently. In English, deleting any two vertices *lowers* `χ`. In Chinese, deleting any two vertices makes `χ` *drop by one*. Both versions are refuted.

**English reading, and the standard Erdős–Lovász notion.** `K₆` is 6-chromatic and edge-critical, and deleting any two vertices leaves `K₄`. It has `15` edges, more than `28/3 = (5·6−2)/3`, so the upper bound fails.

**Both readings.** Every graph in either class has `|E| > (5v−2)/3 + 1`, for two reasons:
- A non-isolated vertex has degree `≥ 5`. Otherwise, take a 5-colouring of `G − uv` and recolour `v`.
- There is at most one isolated vertex. Otherwise, a 5-colouring of `G − x − y` extends to `G`.

Hence `2|E| ≥ 5(v−1)`, with `v ≥ 6`. No graph in either class attains `(5v−2)/3`, not even up to rounding. So the attainment clause is false, and the conjecture fails under both definitions, whatever the uniqueness and girth clauses mean. This holds whether `(5v−2)/3` is read as an upper bound or as a lower bound (Gallai's bound is a lower bound).

Lean: `C3462.conjecture_00000003462_false` (331 lines), using Mathlib's `chromaticNumber`, `deleteEdges` and `induce`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3462/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003462.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3462.conjecture_00000003462_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000003462 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
