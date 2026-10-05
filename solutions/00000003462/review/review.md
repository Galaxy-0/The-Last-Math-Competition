# Solution Review — Conjecture 00000003462 (PR 616)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261004235153`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-05

## Verification

The official bilingual statement, full report, all PDF pages, and all Lean/source files were reviewed. Only the declared submission folder was added. Base metadata marks 00000003462 unsolved and no prior solution existed; the included conjecture is byte-identical to the official source. The PDF was independently rebuilt twice with `xelatex`; both passes exited 0, both versions have four pages, and extracted text agrees after whitespace normalization. The Lean 4.33.1/Mathlib `0df444a…` project was independently linked and built; `lake build`, direct warning-as-error checks, and axiom audits exited 0. The main theorem and principal supporting theorems use only `propext`, `Classical.choice`, and `Quot.sound`. No executable forbidden shortcut or kernel bypass is present. Independent exhaustive coloring checks corroborate all K6 facts; three checksum-manifest entries are stale, but the exact conjecture, current Lean source, and current LaTeX were independently verified.

## Disproof

`K6` is connected, 6-chromatic, and edge-critical; deleting any edge is 5-colorable, and deleting any two vertices leaves K4 with chromatic number 4. Thus it is a genuine six-doubly-critical graph in the literal English and standard Erdős–Lovász readings. It has 15 edges, already exceeding `(5·6−2)/3=28/3`, so the proposed upper bound is false.

Moreover, every graph in the literal English class—and hence the exact-one-drop Chinese subclass—has at most one isolated vertex and every non-isolated vertex has degree at least 5. Therefore `2e≥5(v−1)` and, since `v≥6`, `e>(5v−2)/3+1`. No graph in either class attains the proposed value even up to rounding. Thus the conjecture’s necessary attainment clause fails for arbitrary uniqueness and girth clauses, and also under the lower-bound reading appropriate to Gallai’s bound.

**Disposition: APPROVED.**
