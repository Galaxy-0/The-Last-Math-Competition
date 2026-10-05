# Disprove conjecture 00000004399: the bowtie is a non-complete, non-bipartite common graph of order 5

The conjecture claims that 6 is the minimal order of a non-complete, non-bipartite common graph.
- **Witness.** The bowtie B (two triangles sharing a vertex) has order 5, is connected, is not complete and is not 2-colourable.
- **Counting.** hom(B,G) = Σ_v T(v)², where T(v) counts triangles through v (explicit bijection).
- **Goodman's bound.** Proved by double counting: the triangle counts of G and its complement sum to at least n(n−1)(n−5)/4.
- **Commonness.** With Cauchy–Schwarz this gives t(B,G) + t(B,Gᶜ) ≥ 1/32 − 3/(8n) = 2^{1−e(B)} − O(1/n) for every finite graph G, so B is common in the standard asymptotic sense, and also with any positive eventual bound; the minimality claim fails.
- **Literal uniform reading.** Under "a positive bound over all graphs", the one-vertex graph shows that no non-bipartite graph is common, so the existence claim fails.
- **Main theorem.** `Conjecture4399.conjecture4399_false` (readings `Common`, `CommonPos`, `CommonUniform`).
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 407 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4399/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004399.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture4399.conjecture4399_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004399 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
