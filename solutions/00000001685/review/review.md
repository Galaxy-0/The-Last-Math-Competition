# Solution Review — Conjecture 00000001685 (PR 483)

**Submission:** jilint777 — `jilint777_submission_20261004144326`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the statement calls even subdivisions of K₃,₃ a family of nonplanar Pfaffian graphs and says they help exhaust the crossing-number ≤2 class.
- Path policy: pass — only the submitter's own directory was added; base metadata is unsolved/undisproved.
- LaTeX: independent `latexmk -pdf` build exited 0 after two passes; all 7 pages extracted/rendered and read. No errors or overfull boxes; content agrees with the shipped PDF.
- Lean: core-only Lean 4.19 project independently built with `lake build`; exit 0. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0.
- Axioms: negative conjecture theorems use only `[propext, Quot.sound]`; several explicit positive/computational theorems use none. No extra axioms.
- Forbidden content: no `sorry`, `admit`, `native_decide`, extra axiom, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- Auxiliary code: `python3 verify.py` independently exited 0 with all checks passing. I audited its exact determinant/matching method and separately reproduced the key K33/S parity facts with a different enumeration.

## Semantic audit
The submission proves a general parity obstruction: if a loopless graph has an even number of perfect matchings, every edge occurs in an even number of them, and one orientation has an odd number of negative Pfaffian terms, then every orientation does, so no orientation has all terms one sign. K₃,₃ has six matchings, every edge lies in exactly two, and the natural orientation has three negative terms; hence K₃,₃ is not Pfaffian. If proper subdivisions only are intended, the graph S obtained by replacing one edge with a two-vertex path is also kernel-checked non-Pfaffian. The paper then correctly propagates all three invariants through every two-vertex subdivision and relabeling, proving no even subdivision is Pfaffian.

The Lean definitions use actual edge lists, perfect matching masks, orientation-dependent permutation signs, and either the source's absolute-signed-count definition or the equivalent same-sign Kasteleyn definition. It proves the general obstruction and the K₃,₃/S instances. Non-vacuity is checked through explicit Pfaffian orientations for K₄ and the Wagner graph plus comparisons with recursive skew-matrix Pfaffian expansion. This decisively falsifies the conjecture's even-subdivision clause under both boundary interpretations.

## Issues found
- The all-subdivisions induction and secondary crossing-number example are paper/computation rather than Lean, as the report explicitly states. This is not blocking: Lean alone disproves both the base and proper-subdivision readings, and I verified the omitted induction mathematically.
- The report does not ship a separate byte-for-byte bilingual SOURCE copy, but it quotes the English claim exactly and correctly describes the Chinese version; I compared directly with the official file.

## Disposition
APPROVED — fresh LaTeX, Lean, and Python reproduction all passed; only standard/no axioms occur; and the parity obstruction plus explicit K₃,₃/S instances decisively refute the stated even-subdivision Pfaffian clause.
