# Disprove conjecture 00000002913: degree-d Keller maps over F_q with q > d² need not be injective

- **Keller counterexample.** Over a field of characteristic p, (x^p − x + y^m, y) has Jacobian determinant −1 and degree max(p, m), and sends (0,0) and (1,0) to the same point, so it is not injective.
- **Every degree.** Over F_{2^k} with 2^k > d², the map (x² − x + y^d, y) has degree exactly d, refuting "injective when q > d²" for every d ≥ 2, including the Keller (Jacobian) reading (`keller_counterexample_every_degree`).
- **Other readings.** Without the Jacobian hypothesis the same map fails over every field, prime fields included (`plain_counterexample`); in one variable x^d − x fails (`univariate_counterexample`).
- **Objects.** Mathlib's `MvPolynomial`, `pderiv`, `totalDegree`, `GaloisField` and `Function.Injective`.
- **Not refuted.** The existential reading, Keller maps over prime fields, Adjamagbo's separable variant, d = 1, and the uninterpreted second clause.
- **Main theorem.** `conjecture_00000002913_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 170 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #278 (orionsheep) was merged, then removed in re-audit 541cf4fb with the reason "residue numerals; no field/map/injectivity objects". It used x ↦ x² on F₅ (5 > 2², 1² = 4²), but its Lean theorem was a conjunction of natural-number facts such as (4·4) % 5 = (1·1) % 5. This submission defines plane polynomial maps as pairs of `MvPolynomial (Fin 2) K`, together with their evaluation map, their degree (the maximum total degree) and their formal Jacobian determinant (det of `pderiv`), and it uses `Function.Injective` and Mathlib's finite fields `GaloisField p k` of cardinality p^k. It refutes the threshold clause "a degree-d map over F_q is injective when q > d²" for every d ≥ 2. For arbitrary maps it uses (x² − x + y^d, y) over every field, prime fields included. For Keller maps it uses (x^p − x + y^m, y), which has Jacobian determinant −1 over F_{p^k} with p^k > max(p, m)², so it also covers the Jacobian hypothesis that the definition names. It also gives the one-variable map x^d − x.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2913/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002913.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Tlmc2913.conjecture_00000002913_false`, `Tlmc2913.keller_counterexample_every_degree`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002913 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
