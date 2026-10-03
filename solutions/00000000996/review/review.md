# Solution Review — Conjecture 00000000996 (PR 303)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003091740`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0, warnings-as-errors on)
- [x] No `sorry`, no `native_decide`, no extra axioms (`#print axioms`: `[propext]` only)
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
The universal ratio between the spectral dimension 4/3 of percolation on random graphs and 7/4 of the jungle gym is 7/9 (a universal ratio).

## What the submission proves
The entire literal statement is an arithmetic assertion between three rationals named in the statement itself. In exact rational arithmetic (Lean `Std.Internal.Rat`, kernel-checked):
- `exact_ratio`: (4/3)/(7/4) = 16/21, since 16·9 = 144 ≠ 147 = 7·21 — so the stated ratio is not 7/9;
- `reverse_ratio` / `reversed_claim_also_false`: (7/4)/(4/3) = 21/16 ≠ 7/9, so the reversed reading does not rescue the statement;
- `conjecture996_false : ¬ StatedRatio`.

## Verification notes
Independently rebuilt from the pinned toolchain (Lean 4.19.0, self-contained, no Mathlib): `lake build` exit 0; axiom audit shows exactly `[propext]` for all four theorems; `verify.py` runs (exit 0) and confirms 16/21 ≠ 7/9 and 21/16 ≠ 7/9 with `Fraction`. PDF reviewed — consistent with the Lean. Adjudication note: this is NOT the "vacuous arithmetic" class rejected in PRs #286–#288 — those theorems proved numeric facts while the conjecture's decisive objects (pagenumbers, eigenvalues, ideals) were absent from Lean. Here the statement's only objects are the three constants, all formalized, and the decisive comparison is fully certified. The disproof refutes the statement as written; it establishes no percolation content (the submission says so itself). Minor blemish, not blocking: `verify.py` carries leftover assertions for an unrelated conjecture (00000000425, MacMahon product) alongside the 996 checks.

## Verdict
APPROVED — merged into main (PR 303, merge commit 3bc0e3e0).
