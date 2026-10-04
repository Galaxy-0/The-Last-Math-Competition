# Solution Review — Conjecture 00000008341 (PR 489)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004152400`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — the official formula is literally `2-(w+1)` and gives a negative dimension at `w=2`.
- Eligibility: base metadata is unsolved; PR adds only its own properly named directory.
- LaTeX: independent build exit 0, one A4 page, citations resolved; shipped/fresh content matches.
- Lean: official shared pinned dependencies linked; `lake build` exit 0 (`[2267/2268] Built Main`) and direct warnings-as-errors elaboration exit 0.
- Axioms: only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none.
- Auxiliary computation: none needed.

## Semantic audit

The formal Jarnik set consists of irrationals in `[0,1]` with arbitrarily large denominators and strict error below `q^{-(w+1)}`. The factorial Liouville series is proved irrational, in the unit interval, and a member for every integer `w`, so `W(2)` is nonempty. Since `W(2)⊆R`, its Mathlib Hausdorff dimension is at most one and nonnegative. After proving finiteness, the real-valued dimension is compared to `2-(2+1)=-1`, an impossible equality. This directly refutes the official dimension-conversion conjunct without relying on the deeper classical `2/(w+1)` theorem. Other conjecture clauses are not needed.

## Verdict

APPROVED — the proposed formula is impossible for a nonempty real set, and the exact formal and PDF checks independently pass.
