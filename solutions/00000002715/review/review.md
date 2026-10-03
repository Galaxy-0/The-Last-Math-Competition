# Solution Review — Conjecture 00000002715 (PR 203)

**Submission:** orionsheep — `orionsheep_submission_20261002220314`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
With shellability defined as a linear order of faces whose intersection with previous faces is pure (dim-1), the conjecture states the minimal vertex count of a shellable 3-dimensional manifold complex is twelve.

## What the submission proves
The counterexample is the boundary of the 4-simplex on 5 vertices with the five tetrahedral facets explicit in Lean: the lexicographic facet order is kernel-verified as a shelling under exactly the conjecture's definition, and each vertex link is certified as a tetrahedron boundary (a combinatorial 2-sphere), so a shellable 3-manifold complex exists on 5 < 12 vertices.

## Verification notes
Face structure independently re-enumerated: the lexicographic order is a shelling under the stated pure-(dim-1) condition and every link has exactly 4 triangles. The submission transparently flags the header's "non-shellable" vs the formal sentence's "shellable" discrepancy and refutes the sentence as literally written.

## Verdict
APPROVED — merged into main.

