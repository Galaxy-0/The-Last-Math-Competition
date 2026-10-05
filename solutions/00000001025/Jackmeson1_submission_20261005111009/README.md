# Disprove conjecture 00000001025: the extended binary QR code of length 24 is a second exception (its automorphism group is not PSL(2,23) ⋊ abelian)

The conjecture says q = 7 is the only q for which the automorphism group of the extended QR code is not a semidirect product of PSL(2,q) with a commutative group. It fails at q = 23: the extended binary QR code of length 24 (the extended Golay code W, the span of S_t = (t+N) ∪ {∞} and the all-ones word).
- **Lower bound.** |Aut W| ≥ 24·23·22·21·20·16 = 81,607,680 (`card_aut_ge`), via a stabilizer chain with 11 explicit automorphisms, each certified by `decide +kernel` through a systematic basis.
- **Commutative factor.** A commutative permutation group on 24 points has order ≤ 3⁸ = 6561 (`card_comm_le`; orbit induction with k³ ≤ 3^k).
- **PSL factor.** |PSL(2,23)| ≤ |SL(2,23)| ≤ 12144 (`card_PSL_le`; SL × units injects into GL, Mathlib `card_GL_field`).
- **Conclusion.** Aut W ≇ N ⋊ A and Aut W ≇ A ⋊ N for N = PSL(2, ZMod 23) or PSL(2, ZMod 2) and any commutative A, since 12144·6561 < 81,607,680 (`conjecture_1025_false`).
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 443 lines (about 45 lines of permutation/word data). Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1025/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001025.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1025.conjecture_1025_false`, `C1025.card_aut_ge`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001025 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
