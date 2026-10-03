# Solution Review — Conjecture 00000002042 (PR 210)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261002085129`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
The number of exact covering systems of the integers with pairwise distinct moduli (moduli at most N) is asymptotically c*N^(1/2) with c of the explicit 2/pi type.

## What the submission proves
The Mirsky-Newman-Davenport-Rado theorem is proven in Lean: an exact covering system with pairwise distinct moduli must be the trivial {0 mod 1}. The classical roots-of-unity argument (every non-maximal class contributes 0; the unique max-modulus class contributes L/M != 0 against a vanishing total) is fully formalized, so count N <= 1 for every N and count/(c*sqrt N) -> 0.

## Verification notes
IsExactCovering, DistinctModuli, and the counting function match the conjecture's objects; the re-indexing lemma and cast handling checked. The refutation is a general theorem, not a finite-instance check; any reasonable counting normalization still leaves count <= 1.

## Verdict
APPROVED — merged into main.

