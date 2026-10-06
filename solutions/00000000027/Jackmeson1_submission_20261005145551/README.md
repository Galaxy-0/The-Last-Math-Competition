# Prove conjecture 00000000027: r₃(N) = N·exp(−O(√log N)) (Behrend's bound)

- **Reading.** Literally: r₃(N) = N·e^{−g(N)} with g(N) = O(√log N), where r₃(N) is the maximum size of a subset of [N] = {1..N} with no 3-term progression a, a+d, a+2d (d ≥ 1). Since r₃(N) ≤ N, this is Behrend's (1946) lower bound; this is a proof of a known theorem, with attribution.
- **Lean.** r₃ is defined from scratch and proved equal to Mathlib's `rothNumberNat N` (so the {1..N} and {0..N−1} conventions agree); the claim follows from Mathlib's `Behrend.roth_lower_bound`.
- **Explicit result.** 0 ≤ g(N) ≤ 4√log N for every N ≥ 1, hence `g =O[atTop] √(log N)`.
- **Not claimed.** The matching upper bound r₃(N) ≤ N·e^{−c√log N} (sharpness/Θ), which the one-sided −O(·) notation does not assert.
- **Main theorem.** `C27.conjecture_27`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 137 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture27/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000027.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C27.conjecture_27`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000027 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
