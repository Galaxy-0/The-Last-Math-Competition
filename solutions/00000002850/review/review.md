# Solution Review — Conjecture 00000002850 (PR 206)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261002083415`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
The separation of nonnegative rank from ordinary rank "starts at rank 4", with the minimal separating matrix an explicit 4x4 and a geometric characterization via non-triangulable nested polytopes.

## What the submission proves
The slack matrix of a square is entrywise nonnegative with ordinary rank 3 (row4 = r1-r2+r3; invertible leading 3x3) and nonnegative rank 4 by an airtight fooling-set argument (each diagonal one requires its own rank-1 term), so separation starts at rank 3.

## Verification notes
HasNonnegFactorization and SeparatesAt are the literal conjecture objects; the fooling-set step and both rank bounds checked line by line — the textbook 4-cycle example. Only the "starts at rank 4" clause is refuted, which is the core assertion.

## Verdict
APPROVED — merged into main.

