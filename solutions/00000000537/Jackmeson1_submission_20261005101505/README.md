# Disprove conjecture 00000000537: the bipartite graph K₂ has depth R/I(K₂) ≤ 1 < 2 = ν(K₂)+1

The conjecture says every bipartite graph G satisfies depth R/I(G) ≥ ν(G)+1, where R = k[x_v] and I(G) is the edge ideal.
- **Witness.** G = K₂, a single edge. It is bipartite and ν(K₂) = 1.
- **Depth.** R/I(K₂) = k[x,y]/(xy). If f₁ ∈ m = (x,y) is regular, then u = f₁(x,0) gives a nonzero class in M/f₁M that m annihilates, so no regular sequence of length 2 lies in m, and depth ≤ 1.
- **Generality.** This holds over every field, so the clause fails whatever field is chosen.
- **Definitions in Lean.** `edgeIdeal`, `irrelevantIdeal` and `depth` (an ℕ∞ sup over Mathlib `RingTheory.Sequence.IsRegular` sequences in m, which includes M ≠ (rs)M), and `matchingNumber` (an ℕ∞ sup over `Subgraph.IsMatching`). Bipartite means `Colorable 2`.
- **Main theorems.** `C537.conjecture_537_false`, `C537.K2_counterexample`.
- **Scope.** Only the main clause is refuted; the garbled parenthetical "equality characterization" is not addressed.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 279 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture537/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000537.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C537.conjecture_537_false`, `C537.K2_counterexample`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000537 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
