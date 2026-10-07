# Disprove conjecture 00000001485: the cat-map suspension has zeta radius ≤ 1/2, not 1

- **Claim refuted.** Clause 1: every hyperbolic suspension has ζ with radius of convergence 1. The conjunction therefore fails.
- **Witness.** The suspension flow of Arnold's cat map A = [[2,1],[1,1]] on T² = ℝ²/ℤ², a hyperbolic toral automorphism (`A_hyperbolic`: no eigenvalue of modulus 1).
- **Objects in Lean.** The torus, the cat map as an automorphism, the suspension (T² × ℝ)/((x, t+1) ~ (cat x, t)) with its flow, whose closed orbits are exactly the cat map's periodic orbits (`flow_periodic_iff`), and ζ = ∏_τ (1 − z^{|τ|})⁻¹ over periodic orbits, proved to converge in ℝ⟦z⟧ (`hasProd_zeta`).
- **Periodic counts.** For every n ≥ 1, #Fix(catⁿ) = |det(Aⁿ − I)| ≥ 2ⁿ − 1, via Mathlib's `Submodule.natAbs_det_equiv`.
- **Radius.** n·ζₙ ≥ #Fix(catⁿ), so the radius (`FormalMultilinearSeries.radius`) is ≤ 1/2 (the true value is (3−√5)/2).
- **Not addressed.** The singular-set clause and the "no radius > 1" clause; general Anosov flows beyond the toral subclass; a product over the set of periods without multiplicity.
- **Main theorem.** `C1485.conjecture_00000001485_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 445 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** The earlier submission was PR #262 by orionsheep ("Disproof of conjecture 00000001485", closed without merging on 2026-10-03). The reviewer wrote: "Not merged after review. conjecture_refuted is a conjunction of decidable trivia (four periodic counts, Z[√5] identities, sign flags) that never mentions ζ, the suspension, or a radius of convergence. The cat-map counterexample — valid in prose — is entirely unformalized, and only finitely many periodic counts are certified where the radius of convergence needs all of them." The counterexample is the same one (Arnold's cat map A = [[2,1],[1,1]]), but this submission formalizes every object in Lean/Mathlib. The torus is the quotient group ℝ²/ℤ², and the cat map is an additive automorphism of it. Hyperbolicity is proved: A ∈ GL(2,ℤ) and no complex eigenvalue of A has modulus 1. For every n ≥ 1, the periodic count #Fix(catⁿ) is proved finite and equal to |det(Aⁿ − I)| ≥ 2ⁿ − 1, using Mathlib's index/determinant theorem `Submodule.natAbs_det_equiv`. The suspension flow is built on (T² × ℝ)/((x, t+1) ~ (cat x, t)), and its closed orbits are proved to be exactly the periodic orbits of the cat map, with the same periods. ζ is defined as the infinite product ∏_τ (1 − z^{|τ|})⁻¹ over all periodic orbits τ, a `tprod` in ℝ⟦z⟧ with the coefficientwise topology, and the product is proved to converge (`HasProd`). Finally, the radius of convergence (Mathlib's `FormalMultilinearSeries.radius` of ∑ ζₙ zⁿ) is proved to be ≤ 1/2, so it is not 1. This uses all periodic counts, not finitely many.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1485/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001485.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1485.conjecture_00000001485_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001485 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
