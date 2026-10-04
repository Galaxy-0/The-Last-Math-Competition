# Solution Review — Conjecture 00000001564 (PR 538)

**Submission:** jilint777 — `jilint777_submission_20261004160724`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Verification

Full report/PDF, Lean source, and Python source read. Fresh two-pass PDF compile, exhaustive Python verification, full self-contained Lean build, direct warning-as-error Lean check, and rendering all exited 0. No forbidden proof shortcut occurs; principal theorems use only standard permitted axioms.

## Disproof

The k-dimensional cross-polytope

`C_k = conv{±e_1,...,±e_k}`

is centrally symmetric, k-dimensional, and has exactly `2k` vertices. For any subset `S` of its vertices containing no antipodal pair, `c_S=Σ_{s∈S}s` exposes exactly `S` as a face. Hence `C_k` has the strongest possible cs-neighborliness property and certainly satisfies both the conjecture’s literal definition and standard Grünbaum readings.

But `2k<2^(k+1)` for every `k≥1`. In particular the 3-dimensional octahedron has 6 vertices, not the claimed minimum 16. The Chinese “2k-dimensional” reading is handled by the 6-dimensional cross-polytope, with 12 vertices instead of 16. Lean kernel-checks these cross-polytopes and their exposed-face property; Python independently enumerates faces, lower-bound examples, and Hanner vertex counts.

**Disposition: APPROVED.**
