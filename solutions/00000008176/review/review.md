# Solution Review — Conjecture 00000008176 (PR 322)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261003105651`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0, Mathlib v4.33.1)
- [x] No `sorry`, no `native_decide`, no extra axioms (`#print axioms` exactly `[propext, Classical.choice, Quot.sound]`)
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Clause 2: the zero/nonzero classification of the Artin primitive-root density δ_A(q) is decided by the non-Wieferich criterion W(q): q ≢ 1 (mod p²) for every prime p.

## What the submission proves
The criterion fails in both directions, unconditionally. For every integer s the square s² is a primitive root modulo no odd prime (if p ∣ s the residue is 0; otherwise (s²)^((p−1)/2) = s^(p−1) ≡ 1 by Fermat, so the order divides (p−1)/2 < p−1), hence δ_A(s²) = 0. Yet 4 satisfies W (p² ∣ 3 impossible) with δ_A(4) = 0, refuting "W ⟹ nonzero" under both readings of nonzero (the second via uniqueness of limits); and 9 violates W (9 ≡ 1 mod 2²) with δ_A(9) = 0, refuting the reversed matching. Lean: `artinSet_sq_subset`, `hasPrimeDensity_sq`, `not_classificationNonzero`, `not_classificationNonzero'`, `not_classificationZero`, `conjecture_00000008176_false : ¬ (P ∧ ClassificationNonzero ∧ Q ∧ R)`.

## Verification notes
`lake build` exit 0; axiom audit clean. Real number-theory objects: `IsPrimitiveRoot` in `ZMod p`, density as a limit against `Nat.primeCounting` (squares handled by squeeze against 1/π(x)). The Fermat step and both W evaluations re-derived independently by the reviewer; consistent with the Hooley classification (δ = 0 iff q = −1 or q a square), under which W is simply unrelated. LaTeX consistent; PDF present.

## Verdict
APPROVED — merged into main.
