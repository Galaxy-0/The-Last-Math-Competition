# Solution Review — Conjecture 00000002040 (PR 204)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261002082520`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
A 3-independent set is sum-free. The conjecture asserts the density limit of maximal 3-independent subsets of [n] exists, is at most 1/4, and is exactly 1/4.

## What the submission proves
maxSize n = floor((n+1)/2) is proved for every n (odds are 3-independent; the reflection argument A and {m-a} disjoint in [1,m] gives 2|A|-1 <= m <= n), so the density tends to 1/2, and by uniqueness of limits no limit <= 1/4 exists.

## Verification notes
Fully general (a theorem for all n — no finite sampling), exactly what an asymptotic claim requires. Definitions match the conjecture literally; the reflection lemma and the uniqueness-of-limits contradiction checked line by line.

## Verdict
APPROVED — merged into main.

