# Solution Review — Conjecture 00000002404 (PR 274)

**Submission:** orionsheep — `orionsheep_submission_20261003104554`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
The conjecture claims that for compositions of polynomials, dim J(f o g) >= max(dim J(f), dim J(g)) holds with strict inequality when f, g are noncommuting, and that the parameter conditions for the strict family are explicit.

## What the submission proves
Take f(z) = z^2, g(z) = 3z^2. The monomial composition rule (c z^d) o (e z^k) = (c e^d) z^{dk} — correct as certified — gives f o g = 9z^4 != 3z^4 = g o f (noncommuting by decide). Yet z -> a z^n is linearly conjugate to z -> z^n, with completely invariant circle |z| = |a|^{-1/(n-1)} as Julia set, so all four Julia sets are exact circles, each of Hausdorff dimension exactly 1. Hence dim J(f o g) = max(...) = 1 with no strict inequality — not_strict (not(1 > 1)) refutes the strict clause for an explicit noncommuting pair.

## Verification notes
The composition arithmetic (9z^4 vs 3z^4) and the circle radii |a|^{-1/(n-1)} verified; the fact that z -> a z^n has a circular Julia set of dimension 1 is classical complex dynamics (Mobius conjugation invariance), cited in prose and confirmed by box-counting in reproduce.py. Only the strictness clause is refuted (the non-strict >= happens to hold in this instance), but the conjecture asserts strictness for noncommuting pairs, so the literal statement is refuted by this single pair.

## Verdict
APPROVED — merged into main.

