# Solution Review — Conjecture 00000008413 (PR 417)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004055642`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — the conjecture claims noncyclic abelian Singer-parameter difference sets exist iff `n` is a prime power; `n=2` refutes sufficiency.
- Eligibility: base metadata is unsolved; PR adds only its own properly named directory and no forbidden files.
- LaTeX: independent build exit 0, two US Letter pages, no errors or box warnings; shipped and fresh text/rendered content match.
- Lean: complete independent build exit 0 (`[1179/1180] Built Main`) after official cache staging; direct warnings-as-errors elaboration exit 0.
- Axioms: only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none in source.
- Auxiliary programs: none shipped or needed.

## Semantic audit

At `n=2`, Singer parameters are `(7,3,1)`, so the ambient group must have order 7. Every group of prime order 7 is cyclic, while `2=2^1` is a prime power. Hence the conjecture's asserted prime-power sufficiency for existence on a noncyclic abelian group is false. The Lean definition captures the actual ambient cardinality, block cardinality, and unique ordered nonidentity difference representation. It derives order 7 and cyclicity using Mathlib's real prime-cardinality theorem, then excludes every noncyclic group (a stronger obstruction than the abelian case). The final theorem combines a verified prime-power witness with non-realizability over an actual commutative ambient group and block. The argument is non-vacuous: the defining necessary condition already rules out every eligible noncyclic ambient group. A separate theorem correctly shows no dihedral group has odd order 21.

## Verdict

APPROVED — the prime-order obstruction is correct and exactly matches the official noncyclic-abelian sufficiency claim; all independent PDF and Lean checks pass with only standard permitted axioms.
