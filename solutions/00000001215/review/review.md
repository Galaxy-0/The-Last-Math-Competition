# Solution Review — Conjecture 00000001215 (PR 252)

**Submission:** orionsheep — `orionsheep_submission_20261002162857`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
After recalling Meyniel's conjecture (cop number <= ceil(sqrt n)), the conjecture asserts that the cop number of a planar graph is at most three and tight, and that the cop number of an outerplanar graph is at most two, with only finitely many graphs attaining the bound up to isomorphism.

## What the submission proves
The submission refutes the finitude clause: the cycles C_n (n >= 4) are outerplanar, pairwise non-isomorphic, and each has cop number exactly 2, so infinitely many pairwise non-isomorphic outerplanar graphs attain the bound. In Lean: robber_mirror/one_cop_never_wins prove for ALL n and all cycle structures that a single cop never forces capture; for C_5 a complete 125-state two-cop certificate (capT5/strat5 by kernel decide, capT_sound by induction) shows capture within 2 rounds from every state, so cop(C_5) = 2 exactly.

## Verification notes
Game semantics independently recomputed; the reviewer's retrograde recomputation of the full capture-horizon table for C_5 matches the Lean capT5 table on all 125 entries, and all 125 strategy moves are legal and decreasing. reproduce.py verifies cop number exactly 2 for C_4 through C_21. Only trivially-true steps (outerplanarity of cycles, two-cop sweeping) are prose-bridged; the subtle direction is entirely kernel-certified. Note: the PR contained two folders; the companion tex/PDF/README from the sibling folder were consolidated into this audited submission folder during merge.

## Verdict
APPROVED — merged into main.

