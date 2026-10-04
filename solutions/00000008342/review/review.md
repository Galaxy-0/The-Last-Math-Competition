# Solution Review — Conjecture 00000008342 (PR 492)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004153000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — the stated maximal-coordinate height asymptotic fails on positive square radii.
- Eligibility: base metadata is unsolved; PR adds only its own properly named directory.
- LaTeX: independent build exit 0, two A4 pages, no substantive warnings; shipped/fresh content matches.
- Lean: official shared pinned dependencies linked; `lake build` exit 0 (`[1802/1803] Built Main`) and direct warnings-as-errors elaboration exit 0.
- Axioms: only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none.
- Auxiliary computation: none needed.

## Semantic audit

For every `n`, `(n,0,0)` lies on `x²+y²+z²=n²` and attains height `n`, while every point on that sphere has all absolute coordinates at most `n`; Lean proves the exact supremum `H(n²)=n`. Hence `H(n²)/sqrt(n²/3)=sqrt3`, a constant different from 1, along parameters tending to infinity. This disproves the claimed asymptotic. If the one-third wording is interpreted as an additional factor, the ratio is `3sqrt3`, also different from 1. The formalization uses the actual integer sphere, maximum coordinate, and supremum, not a typical or average value, and establishes both asymptotic failures.

## Verdict

APPROVED — the square-radius family gives an exact, fully formal counterexample to the maximal-height asymptotic.
