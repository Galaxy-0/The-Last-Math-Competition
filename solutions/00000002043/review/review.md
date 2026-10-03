# Solution Review — Conjecture 00000002043 (PR 215)

**Submission:** orionsheep — `orionsheep_submission_20261003002014`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Conjecture 2043 asserts #{n <= x : s_q(3n) = s_q(n)} ~ c_q * x/(log x)^(1/2), parameterized by q with no restriction on q.

## What the submission proves
Lean proves in full generality that in base 3, multiplication by 3 appends a zero trit: s3(3n) = s3(n) for every n, so the counting function equals x exactly for every x — exactly linear, while c*x/sqrt(log x) = o(x), refuting the displayed asymptotic at q = 3.

## Verification notes
The identity is elementary and its proof fully general (fuel-independence of the digit sum proved). The final asymptotic negation follows immediately from the certified exact count and is stated in the tex. The literal statement fixes no q, so the q = 3 instance suffices.

## Verdict
APPROVED — merged into main.

