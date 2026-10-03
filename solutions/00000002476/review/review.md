# Solution Review — Conjecture 00000002476 (PR 213)

**Submission:** orionsheep — `orionsheep_submission_20261003000758`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Conjecture 2476 asserts the Glaisher correspondence merges repeated parts into odd parts and that "the merging map preserves part counts".

## What the submission proves
The Lean defines the standard Glaisher merge (expand each multiplicity in binary over the set bits) and kernel-certifies the counterexample [3,3] -> [6]: both partitions of 6, [3,3] odd-parts, part counts 2 vs 1 — not preserved. Additional certified instances and a script sweep of all partitions of n <= 40.

## Verification notes
The map defined is the classical Glaisher involution's merging step; failure of part-count preservation on one instance refutes the universal claim. The tex honestly scopes the refutation to the "preserves part counts" clause only.

## Verdict
APPROVED — merged into main.

