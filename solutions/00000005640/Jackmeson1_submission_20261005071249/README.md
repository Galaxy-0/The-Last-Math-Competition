# Disprove conjecture 00000005640: an intersection-preserving redrawing pair always has isomorphic intersection graphs

The conjecture asks for two convex-set families with the same intersection spectrum but non-isomorphic intersection graphs, where the separation is realized by an explicit redrawing pair that preserves intersections. This is impossible.
- **Reading.** A redrawing pair preserving intersections is a bijection `σ` of members with `F_i ∩ F_j ≠ ∅ ⇔ G_σ(i) ∩ G_σ(j) ≠ ∅` for distinct members.
- **Key fact.** Such a `σ` is an isomorphism of the intersection graphs (`isoOfPreserves`). So the final clause contradicts "non-isomorphic intersection graphs".
- **Generality.** "Intersection spectrum" is undefined, so it is kept as an arbitrary relation. Dimensions are arbitrary and families may be infinite. The separating pair and the redrawing pair may be the same (`conjecture5640_false`) or different (`conjecture5640_separate_false`).
- **Further readings.**
  - Nerve reading: `nerve_redrawing_iso`.
  - One-sided reading with equal edge counts: `oneSided_redrawing_iso`.
  - In particular, the adjacency-spectrum case: `oneSided_adjSpectrum_iso`, via trace(A²) = 2|E|.
- **Not refuted.** The one-sided reading with a spectrum that does not fix the edge count.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.
- **Credit.** The transport idea follows the accepted disproof of 00000005400.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture5640/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000005640.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture5640.conjecture5640_false`, `Conjecture5640.conjecture5640_separate_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000005640 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
