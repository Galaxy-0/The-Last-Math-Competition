# Disprove conjecture 00000002591: no finite poset with n ≥ 3 elements has 2ⁿ Dedekind–MacNeille cuts

The conjecture claims (clause iii) that the number E(n) of isomorphism types of n-element posets P with |DM(P)| = 2ⁿ grows superpolynomially.
- **Definitions.** DM(P) is Mathlib's `DedekindCut P` (pairs (A,B) with A^u = B and B^l = A); a set is a left set iff `lowerBounds (upperBounds A) = A`. E(n) counts partial orders on `Fin n` with at least 2ⁿ cuts, modulo order isomorphism (the quotient is proved finite).
- **Argument.** If all 2ⁿ subsets are cuts, each closed singleton {x} forces Iic x = {x}, so P is an antichain; then {x,y} has no upper bound and its closure is P, so n ≤ 2.
- **Consequence.** |DM(P)| < 2ⁿ for n ≥ 3 (`card_cuts_lt`), E(n) = 0 for n ≥ 3, and E is neither eventually above every n^k nor infinitely often above C·n^k (`not_superpolynomial`). The labelled count is also 0.
- **Also proved.** Clause (i) for finite posets, |DM(P)| ≤ 2^|P| (`card_cuts_le`); finite antichains with ≥ 3 elements have only n+2 < 2ⁿ cuts. Non-vacuity: the 2-element antichain attains 4 = 2² (`antichain2_attains`, `E_two_pos`).
- **Scope.** Not addressed: clause (ii) for infinite posets, and the vague clause (iv) on "three-chain cross products".
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 206 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2591/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002591.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture2591.not_superpolynomial`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002591 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
