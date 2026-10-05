# Prove conjecture 00000006320: Ω₂ and Ω₂⁺ share the permanent lower bound 1/2 but have different support families

This proves the conjecture with an explicit pair of matrix classes. The first is Ω₂, the 2×2 doubly stochastic matrices (Mathlib `doublyStochastic`). The second is Ω₂⁺, the subclass whose entries are all positive.
- **Same constant.** Every M ∈ Ω₂ has the form [[a,1−a],[1−a,a]], so perm M = a² + (1−a)² ≥ 1/2. Equality holds at J/2, which lies in Ω₂⁺. So 1/2 = 2!/2² is the least permanent in both classes (`IsLeast`), and `lbConst` (the sInf) agrees.
- **Different supports.** `suppFamily Omega2 = {diag, antidiag, full}` and `suppFamily Omega2pos = {full}`. The identity has diagonal support, which occurs only in Ω₂.
- **Main theorem:** `separation`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture6320/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000006320.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture6320.separation`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000006320 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
