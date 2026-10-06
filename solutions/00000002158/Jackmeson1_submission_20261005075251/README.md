# Disprove conjecture 00000002158: the chromatic threshold of C5-free graphs is at most 1/6, not 1/5

The conjecture says the chromatic threshold of C₅-free graphs (the minimum-degree ratio above which the chromatic number stays bounded) is 1/5.
- **Definition (ABGKM, arXiv:1108.1746, quoted).** δ_χ(H) = inf{d > 0 : ∃K, every H-free G on n vertices with δ(G) ≥ d·n is K-colourable}. H-free is Mathlib's `H.Free G` (no subgraph copy).
- **Result.** d = 1/6 is admissible with K = 264, so δ_χ(C₅) ≤ 1/6 < 1/5.
- **Argument.** Take a maximum set S whose members pairwise share at most 2 neighbours. Two adjacent vertices that each share ≥ 3 neighbours with the same s ∈ S would close a C₅, so colouring every vertex by such a witness in S is proper. Counting private neighbourhoods gives |T|·δ ≤ n + 2|T|(|T|−1) for T ⊆ S, so |S| ≤ 11 once n > 264, i.e. at most 22 colours.
- **Induced reading.** Complete graphs have no induced C₅, so that threshold is exactly 1 ≠ 1/5 (`chromaticThresholdInd_cycle5`).
- **Main theorems:** `C2158.chromaticThreshold_cycle5_ne`, `C2158.chromaticThresholdInd_cycle5`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 246 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2158/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002158.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2158.chromaticThreshold_cycle5_ne`, `C2158.chromaticThresholdInd_cycle5`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002158 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
