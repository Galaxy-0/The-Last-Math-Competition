# Solution Review — Conjecture 00000008347 (PR 494)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004153900`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — the claimed reciprocal Hurwitz spectrum omits zero, but Liouville numbers attain zero.
- Eligibility: base metadata is unsolved; PR adds only its own properly named directory.
- LaTeX: independent build exit 0, two A4 pages, citation resolved; shipped/fresh content matches.
- Lean: official shared pinned dependencies linked; `lake build` exit 0 (`[2042/2043] Built Main`) and direct warnings-as-errors elaboration exit 0.
- Axioms: only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none.
- Auxiliary computation: none needed.

## Semantic audit

The formal reciprocal constant is `liminf q*distance(qα,Z)`. For the Liouville number `L=Σ10^{-n!}`, exponent-three approximations at arbitrarily large denominators give `q*||qL||Z < q²|L-p/q| < q^{-1}`. Errors are nonnegative and, for every positive ε, frequently below ε, so the liminf is exactly zero. Thus the irrational `L` places zero in the actual spectrum and its closure. Since zero is not in `[1/√5,1/2]`, the conjectured closed interval is false. Lean proves nearest-integer minimization, the approximation scaling, the liminf, irrationality, spectrum membership, closure membership, and final set inequality using genuine definitions. The report states the reciprocal-zero convention and the all-irrational scope explicitly.

## Verdict

APPROVED — the Liouville-zero counterexample is mathematically decisive and fully independently reproducible.
