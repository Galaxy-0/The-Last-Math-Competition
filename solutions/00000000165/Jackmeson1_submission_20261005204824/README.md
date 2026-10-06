# Disprove conjecture 00000000165: the sum-cover number of the d-th power subgroup is not (1+o(1))·log p/(log p − log d)

- **Objects.** H = the subgroup of d-th powers of F_p^× (range of `powMonoidHom d`); K(p,d) = the least k ≥ 1 with k-fold sumset k•H = F_p; L = log p/(log p − log d). The Chinese "k 次幂" is read as d-th powers (an evident slip), not exploited.
- **Reading.** For each fixed ε ∈ (0,1), |K/L − 1| → 0 uniformly over primes p and d | p−1 with d < p^{1−ε}, as d → ∞. Refuted for every ε ∈ (0,1).
- **Family.** By Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_eq_mod`): d = 2(N+2) and a prime p > d^d with p ≡ d+1 (mod 2d), so (p−1)/d is odd and −1 is not a d-th power. Hence 0 ∉ H and 0 ∉ H+H, so K ≥ 3; a cover exists by Cauchy–Davenport (`ZMod.cauchy_davenport`, |H| ≥ 2), so K is a true minimum.
- **Contradiction.** In this family 1 < L ≤ 4/3 and d < p^{1−ε}, so K/L ≥ 9/4 and the (1+o(1)) claim fails.
- **Variants.** Also refuted: K against ⌈L⌉, ⌊L⌋ and round(L); the "at most k summands" variant (sumsets of H ∪ {0}) against L, ⌊L⌋, round(L). Not refuted: that variant against ⌈L⌉, and readings adding a lower bound on d (our family has log d/log p → 0).
- **Main theorems.** `C165.not_conjecture165`, `C165.main`, `C165.family`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 309 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture165/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000165.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C165.not_conjecture165`, `C165.main`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000165 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
