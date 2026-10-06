# Disprove conjecture 00000008185: G(k) ≠ k for every k ≥ 2, so "G(k) = k" has no threshold k ≥ 7

The conjecture is a conjunction of three laws. The third says the generalization `G(k) = k` of `G(4) = 16` "first holds at threshold k ≥ 7", where `G(k)` is Hardy–Littlewood's: the least `s` such that every sufficiently large integer is a sum of at most `s` positive `k`-th powers.
- **Key fact (proved from scratch).** For every `k ≥ 2` and every `M`, some `n ≥ M` is not a sum of at most `k` positive `k`-th powers. Counting: the `n ≤ t^k` that are such sums come from at most `C(t+k, k)` multisets of bases, and with `t = 3k + 4^k M` one gets `C(t+k,k) + M ≤ t^k`. Hence `G(k) ≠ k` for every `k ≥ 2`, and `G(k) ≥ k + 1` once some `s` suffices. Also `G(1) = 1`.
- **Readings refuted.** `G(7) = 7`; `G(k) = k` for all `k ≥ 7`; for all `k` beyond some `K ≥ 7`; "the least `k ≥ 2` with `G(k) = k` exists and is `≥ 7`"; "the least `k ≥ 1` with `G(k) = k` is `≥ 7`".
- **Main theorem.** `C8185.conjecture_8185_false`, over `waringG k = sInf {s | Suffices k s}`.
- **Scope.** `G(k) = k` is read literally, as both languages write it. Garbled alternatives (`4k`, `k²`, `2^k`, `k+1`) are not refuted. Laws 1 and 2 are not addressed; refuting law 3 refutes the conjunction.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 179 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture8185/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000008185.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C8185.conjecture_8185_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000008185 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
