# Disprove conjecture 00000003991: functional PHP_n has cutting-plane refutations of polynomial length, so no 2^{n/8} lower bound

- **Proof system.** Cutting Planes built from scratch (Boolean axioms, positive integer combinations, division with ceiling rounding; length = number of lines), following the definitions quoted from Dantchev–Galesi–Ghani–Martin (arXiv:2102.07622, citing Cook–Coullard–Turán 1987) and Beame et al. (arXiv:1710.03219).
- **Faithfulness.** Functional PHP_n (pigeon, hole and functionality axioms) is encoded, and its 0/1 solutions are exactly the graphs of injections Fin(n+1) → Fin n (`fphp_sat_iff`).
- **Short refutation.** For every n ≥ 1: for each hole, derive −Σᵢ x_{ij} ≥ −1 by rounding (m−1)T_m + Σ hole axioms by m, then add the pigeon axioms; length ≤ 8n³ and every coefficient ≤ 2n (`fphp_short_refutation`).
- **Refutation.** No lower bound c·2^{εn} holds for any c, ε > 0, even with coefficients bounded by 2n (`no_exponential_lower_bound`); in particular 2^{n/8} fails for plain CP and for polynomially bounded coefficients (`conjecture_3991_false`); concretely 8n³ < 2^{n/8} for all n ≥ 209.
- **Not addressed.** Coefficients bounded by an absolute constant; clause 2 on its own (consistent with our result). DGGM's rule table writes b ∈ ℤ⁺ in the rounding rule; any integer b is allowed, as in Beame et al.
- **Main theorem.** `C3991.conjecture_3991_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 521 lines (about 75 for the faithfulness theorem). Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3991/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003991.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3991.conjecture_3991_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003991 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
