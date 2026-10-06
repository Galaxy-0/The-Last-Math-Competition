# Disprove conjecture 00000001680: at the connectivity threshold, random geometric graphs have treewidth ≥ c·log n, not O(√(log n / log log n))

- **Claim refuted.** tw = Θ(√(log n / log log n)) for random geometric graphs at the connectivity threshold. The upper half O(·) fails deterministically, which refutes the Θ claim; the (true, weaker) lower half is not addressed.
- **Setting.** At least n/2 points anywhere in a box [−L,L]² (covers the unit square, the unit disk and the binomial model; Poisson on the event N ≥ n/2), Euclidean distance, any radius r > 0 with n·r² ≥ c₀·log n for any fixed c₀ > 0.
- **Grid argument.** Squares of side r/2 give O(n/log n) cells; some cell holds ≥ c·log n points, pairwise within distance r: a clique.
- **Treewidth.** The standard tree-decomposition definition (a finite Mathlib `IsTree`, vertex and edge coverage, connected node sets per vertex; tw = min over decompositions of largest bag − 1). The Helly property of subtrees puts every clique in one bag, so ω ≤ tw + 1, hence log n ≤ (64L²/c₀ + 4)(tw + 1) for every placement.
- **Result.** For every constant C and all n ≥ N(C), tw > C·√(log n / log log n) for every placement; so the event "tw ≤ C·√(log n / log log n)" has probability 0 under any distribution (`prob_upper_bound_eq_zero`). The bound also holds for every supergraph of the unit-disk graph (e.g. the torus graph).
- **Context.** Mitsche–Perarnau (STACS 2012, retrieved Dagstuhl abstract): tw = Θ(r√n) in [0,√n]², i.e. Θ(√(n log n)) at the connectivity threshold.
- **Main theorem.** `C1680.treewidth_not_upper_bound`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 425 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1680/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001680.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1680.treewidth_not_upper_bound`, `C1680.prob_upper_bound_eq_zero`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001680 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
