# Disprove conjecture 00000000716: the sign of Γ_p(a)Γ_p(1−a) is not a function of p mod 4

- **Object.** Morita's p-adic gamma function is built in Lean as Γ_p(x) = lim_k mor_p(appr x k), where mor_p(n) = (−1)^n ∏_{0<j<n, p∤j} j, via a generalized Wilson theorem (the units of ZMod p^k multiply to −1 for odd p) and the Morita congruence; Γ_p is proved continuous, equal to mor_p on ℕ (`gammaP_natCast`), and the unique such continuous function (`gammaP_unique`).
- **Reading (A).** For every odd prime p, Γ_p(1)Γ_p(0) = −1 but Γ_p(2)Γ_p(−1) ≡ 1 (mod p), so the product depends on a and no function of p mod 4 fits (`not_function_of_p_mod_four`, `reflection_product_not_constant`).
- **Reading (B).** For the fixed integer a = 4 the sign is −1 for p = 3 and +1 for p = 7, although 3 ≡ 7 (mod 4) (`not_function_of_p_mod_four_at_four`).
- **Not refuted.** The special case a = 1/2, which is true (Γ_p(1/2)² = (−1)^{(p+1)/2}).
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 350 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture716/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000716.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C716.not_function_of_p_mod_four`, `C716.not_function_of_p_mod_four_at_four`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000716 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
