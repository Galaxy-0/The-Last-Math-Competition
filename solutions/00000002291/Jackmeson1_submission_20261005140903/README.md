# Disprove conjecture 00000002291: centralizers in simple groups are not bounded below by |G|^{1/2}/8 (all elements or involutions only), and A5 does not attain c = 1/8

- **Reading R1 (all nonidentity x in a nonabelian finite simple group of even order): false.** In A₉ the 9-cycle has |C(x)| ≤ 9 < √181440/8 ≈ 53.2. For every c > 0, the n-cycle in A_n (n = 2m+1, m = ⌈1/c²⌉+2) has |C(x)| ≤ n < c·√|A_n|.
- **Reading R2 (involutions only): false.** G = PSL(2,128) (simple by Mathlib's `rank_two_simple`, nonabelian, even order) contains the involution t = image of [[1,1],[0,1]], with |C(t)| ≤ 128 < √|G|/8 ≈ 181. For every c > 0, PSL(2,2^k) with k = ⌈1/c²⌉+2 has an involution t with |C(t)| < c·√|G|.
- **Characteristic-2 facts in Lean.** Z(SL(2,F)) = 1, so SL(2,F) ≃* PSL(2,F). The centralizer of [[1,1],[0,1]] in SL(2,F) is {[[1,b],[0,1]]}, of order ≤ q. |SL(2,F)| ≥ (q−1)q².
- **Tightness clause.** "Attained by … involutions of A₅" is false: every x in A₅ has |C(x)| ≥ 1 > √60/8, and every nonidentity x has |C(x)| ≥ 2 > 2·√60/8.
- **Main theorem.** `C2291.conjecture_2291_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 446 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #271 by orionsheep for this conjecture (it argued from PSL(2,139)) was merged and then removed in the full re-audit (commit 541cf4fb). The re-audit's reason: "numeral comparisons; no groups". Its Lean defined no group, no centralizer and no simplicity, and compared only numerals. This submission formalizes the objects for both readings of the bound. For all nonidentity elements it uses the alternating groups A_n (simplicity from Mathlib, centralizer orders via Mathlib's cycle-type formula) with n-cycles. For involutions only it uses PSL(2, F) over characteristic-2 fields (simplicity from Mathlib's `rank_two_simple`, trivial center, and the centralizer of a transvection computed in Lean). It also refutes the claim that the constant is attained by involutions of A5.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2291/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002291.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2291.conjecture_2291_false`, `C2291.not_lowerBoundInvolutions`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002291 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
