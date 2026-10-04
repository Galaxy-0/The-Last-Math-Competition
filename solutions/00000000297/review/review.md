# Solution Review — Conjecture 00000000297 (PR 537)

**Submission:** jilint777 — `jilint777_submission_20261004161822`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Verification

Full report/PDF, Lean source, and Python source read. Fresh two-pass PDF compile, exhaustive Python verification, full self-contained Lean build, direct warning-as-error check, and page rendering all exited 0. No forbidden proof shortcut occurs, and principal theorems use only standard permitted axioms.

## Disproof

For any two Wang tiles, if both horizontal cross-matches fail to hold, every tile in any legal tiling must match itself horizontally; otherwise its two neighbors would both be the other tile, forcing both cross-matches. The analogous vertical lemma holds.

The resulting four cases always construct a legal tiling with periods `(2,0)` and `(0,2)`: checkerboard when both directions cross; constant tiling when neither crosses; horizontal or vertical stripes in the mixed cases. Therefore every tilable set of at most two Wang tiles has a periodic (indeed doubly periodic) tiling and cannot be aperiodic. This refutes the conjecture’s asserted 2-tile aperiodic set and its minimum-2 clause.

Lean formalizes arbitrary colors, matching, tilings, periods, strong/weak aperiodicity, all ≤2-tile cases, clause 1 failure, the true one-tile clause, and non-vacuity examples. Python independently exhausts all relation pairs and concrete tile pairs.

**Disposition: APPROVED.**
