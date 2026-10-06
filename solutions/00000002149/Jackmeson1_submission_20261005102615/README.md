# Disprove conjecture 00000002149: μ(Ḡ) ≤ |V| − ω(G) − 1 fails for complete and edgeless graphs

- **Parameter.** μ is the standard Colin de Verdière parameter (sign pattern, exactly one negative eigenvalue with multiplicity, Strong Arnold Hypothesis), defined in Lean as the largest admissible corank.
- **The claimed tight case fails.** For G = K_n (n ≥ 1) the bound is −1, but diag(−1,0,1,…,1) is admissible for the edgeless complement, so μ ≥ 1 for n ≥ 2 (μ ≥ 0 for n = 1).
- **Edgeless graphs.** For G edgeless on n ≥ 2 vertices the bound is n − 2, but −J is admissible for K_n with corank n − 1: since J² = nJ and the trace is −n, exactly one eigenvalue is −n and the rest are 0.
- **Substance.** Explicit admissible matrices are given, so the result does not rest on μ being ℕ-valued in Lean.
- **Main theorem.** `C2149.conjecture_2149_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 234 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2149/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002149.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2149.conjecture_2149_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002149 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
