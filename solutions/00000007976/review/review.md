# Solution Review — Conjecture 00000007976 (PR 327)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261003113414`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0, Mathlib v4.33.1)
- [x] No `sorry`, no `native_decide`, no extra axioms (`#print axioms` exactly `[propext, Classical.choice, Quot.sound]`)
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Clause 3: the exact value of the radius-1 binary covering density is μ(n,1) = 1 + 2⁻ⁿ (the "Rosenbloom type" realization).

## What the submission proves
The claim fails at every odd n, for every code: the density |C|·(n+1)/2ⁿ equaling 1 + 2⁻ⁿ forces |C|(n+1) = 2ⁿ + 1, whose left side is even (n + 1 even) and right side odd. So μ(n,1) ≠ 1 + 2⁻ⁿ at n = 1 and at arbitrarily large odd n — both the "for all n" and the "for all large n" readings fail. The true values are also certified: the sphere-covering bound K(n,1)(n+1) ≥ 2ⁿ is proven by genuine ball counting, and μ(3,1) = μ(7,1) = 1 via the repetition code {000, 111} and the [7,4] Hamming code (parity-check columns = binary expansions, card 16 and covering decided over all 128 words). Lean: `density`, `coveringNumber`, `mu`, `parity_contra`, `density_ne`, `mu_ne`, `sphere_covering`, `mu_eq_one_of_perfect`, `mu_three`, `mu_seven`, `not_claim3`, `not_claim3Eventually`, `conjecture_00000007976_false`.

## Verification notes
`lake build` exit 0; axiom audit clean. The parity step is tied to the actual objects — the integer equation is extracted from the ℝ-equality by `field_simp` + cast, and the refutation applies to μ itself (via K) as well as to any individual code. The reviewer verified μ(3,1) = 1 (2·4 = 8) and μ(7,1) = 1 (16·8 = 128) by hand, and the parity obstruction (even = odd) is immediate. The "even vs odd" arithmetic here is the mathematical content of the claim, not a vacuous stand-in: density, K and μ are fully defined. LaTeX consistent; PDF present.

## Verdict
APPROVED — merged into main.
