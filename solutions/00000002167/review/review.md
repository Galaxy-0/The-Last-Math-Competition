# Solution Review — Conjecture 00000002167 (PR 612)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261004233829`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-05

## Verification

The official bilingual conjecture, full LaTeX, all PDF pages, and all Lean/source files were reviewed. Only the declared submission folder was added. Base metadata marks 00000002167 unsolved and no prior solution existed.

The PDF was independently rebuilt twice with `xelatex`; both passes and the build exited 0. The submitted and rebuilt PDFs each have three pages, and their extracted text is identical after whitespace normalization. The Lean project was independently copied, linked to the required Lean 4.33/Mathlib `0df444a…` dependencies, and built with `lake build`; the build exited 0. Direct warning-as-error checks for `Conjecture2167/Basic.lean` and `Conjecture2167.lean` also exited 0. The audited main theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. No executable `sorry`, `admit`, `native_decide`, custom axiom, `unsafe`, `implemented_by`, `extern`, `skipKernelTC`, or kernel bypass is present.

The submitted SHA manifest has stale hashes for `conjecture.md` and `Basic.lean`; nevertheless the actual conjecture file is byte-identical to the official bilingual source and the actual Lean source passes all independent checks. This is a non-blocking hygiene defect.

## Disproof

In a graph of girth at least 5, the second-neighborhood sets `N(l)\{i}` over neighbors `l` of `i` are pairwise disjoint and avoid `{i}∪N(i)`, because intersections would create a 4-cycle or triangle. Therefore `∑_{l∼i} deg(l)≤n−1`. Applying this at a maximum-modulus coordinate of an adjacency eigenvector gives spectral radius at most `√(n−1)`, hence at most 2 on five vertices.

Both `C5` and `K1,4` have girth at least 5 and are connected. They have adjacency eigenvalue 2 with eigenvectors `(1,1,1,1,1)` and `(2,1,1,1,1)`, respectively. Thus both attain the universal five-vertex maximum. They have 5 and 4 edges and are not isomorphic. This non-vacuously refutes the conjecture’s explicit all-`n≥5` uniqueness clause, even after adding a connectedness restriction.

**Disposition: APPROVED.**
