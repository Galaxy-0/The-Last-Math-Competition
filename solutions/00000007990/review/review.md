# Solution Review — Conjecture 00000007990 (PR 328)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261003113826`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0, Mathlib v4.33.1)
- [x] No `sorry`, no `native_decide`, no extra axioms (`#print axioms` exactly `[propext, Classical.choice, Quot.sound]`)
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Clause 1: perfect Lee codes PL(n,e) exist only at (n,e) = (2,2), at e = 2 with n ≡ ±1 (mod 6), and at sparse higher-radius (e ≥ 3) exceptions. In particular, no radius-1 perfect Lee code exists.

## What the submission proves
Radius-1 perfect Lee codes exist in every dimension: the classical Golomb–Welch construction C_n = {x ∈ ℤⁿ : Σᵢ (i+1)xᵢ ≡ 0 (mod 2n+1)} is perfect of radius 1 for every n ≥ 1, proven **generally** (not by instances). The 2n+1 points x, x ± eᵢ have weights w(x) + ε, ε ∈ {0, ±1, …, ±n}, which are pairwise distinct mod 2n+1 (`stepWeight_injective`, using 2n+1 odd); for each residue s of w(x) a step with weight ≡ −s is constructed explicitly (three cases); uniqueness follows from |ΔstepWeight| ≤ 2n < 2n+1 and `Int.eq_zero_of_abs_lt_dvd`. Every (n,1) violates the claimed list — `claim1_fails_everywhere` shows the failure is not sparse. Lean: `leeDist`, `IsPerfectLeeCode`, `GW`, `isPerfectLeeCode_GW`, `not_claim1`, `claim1_fails_everywhere`, `conjecture_00000007990_false : ¬ (Claim1 ∧ P ∧ Q)`.

## Verification notes
`lake build` exit 0; axiom audit clean. The reviewer verified the construction independently (Golomb–Welch 1970): the kernel of the surjective weight functional has index 2n+1, matching the Lee-ball size, so balls tile ℤⁿ. The Chinese conjecture text confirms "higher radius" means e ≥ 3, so radius 1 is excluded by the claimed list under every reading; allowing all e ≥ 3 only weakens the claim. The formalization is a genuine lattice/code construction over `Fin n → ℤ`. LaTeX consistent; PDF present.

## Verdict
APPROVED — merged into main.
