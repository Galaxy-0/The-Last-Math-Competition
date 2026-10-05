# Disprove conjecture 00000003423: adding an edge can increase hitting times

- **Witness.** On the path P₅ = 0–1–2–3–4, H(0→4) = 16 and max_{a,b} H(a→b) = 16. After adding the single edge {0,2}, the hitting-time vector to 4 is (18,18,16,9,0), so H(0→4) = 18 and the maximum is at least 18.
- **Consequence.** "Adding edges decreases hitting time" fails for pairwise hitting times and for the maximal hitting time, so the submodularity clause is moot. The K_n clause (n−1) is true and not disputed.
- **Objects in Lean.** Mathlib `SimpleGraph`s (`pathGraph 5`, `pathGraph 5 ⊔ edge 0 2`); the simple random walk's first-step system h(b) = 0, h(v) = 1 + (1/deg v)·Σ_{u~v} h(u); a general proof that it has exactly one solution on every connected finite graph (maximum principle, then injective ⇒ surjective); `hittingTime` defined as that solution.
- **Scope.** The identification with E_a[τ_b] is the standard first-step argument, given in prose. Commute times are not covered.
- **Main theorems.** `C3423.not_edge_monotone_hittingTime`, `C3423.not_edge_monotone_maxHittingTime`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 242 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #224 by orionsheep used P₃ → K₃, where adding the edge {1,3} raises H(1→2) from 1 to 2, and was closed without merging. The reviewer's reason: "the Lean theorems are 2*2 = 2+2 (twice), 2*2−1 ≠ 0, 1 = 1, 2 > 1; graphs, random walks, and hitting times appear nowhere, so the P₃-vs-K₃ counterexample is exclusively prose." This submission formalizes Mathlib simple graphs, the first-step hitting-time system of the simple random walk (h(b) = 0, h(v) = 1 + (1/deg v)·Σ_{u~v} h(u)), and a general theorem that this system has exactly one solution on every connected finite graph (maximum principle plus finite-dimensional linear algebra). The hitting time is defined as that solution. The example is also replaced: in P₃ → K₃ the maximal hitting time drops from 4 to 2. Here, adding the chord {0,2} to the path P₅ raises H(0→4) from 16 to 18 and the maximal hitting time from 16 to at least 18. Both are proved in Lean, refuting edge-monotonicity for pairwise hitting times and for the maximal hitting time.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3423/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003423.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3423.not_edge_monotone_hittingTime`, `C3423.not_edge_monotone_maxHittingTime`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003423 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
