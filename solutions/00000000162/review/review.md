# Solution Review — Conjecture 00000000162 (PR 200)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261002063847`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
For every n >= 3 there exists a planar convex n-gon whose side vectors all have prime squared lengths — two-squares vectors with a^2+b^2 = p for primes p = 1 mod 4 — summing to zero.

## What the submission proves
A parity argument valid for all n: a prime p = 1 mod 4 is odd, so a^2+b^2 = p forces exactly one of a, b odd (a+b odd, proved in ZMod 2); a zero-sum forces the total coordinate sum even, but it is a sum of n odd numbers, so n must be even. Instantiated at n = 3, no such polygon exists, convex or not.

## Verification notes
Fully general Lean argument (no finite-instance dependence); the single failing value n = 3 refutes the "for every n >= 3" claim, and discarding convexity only strengthens the result. The writeup honestly discusses the p = 2 reading, under which the conjecture would survive, and refutes the statement as qualified.

## Verdict
APPROVED — merged into main.

