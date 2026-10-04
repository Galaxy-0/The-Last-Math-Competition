# Solution Review — Conjecture 00000007145 (PR 473)

**Submission:** jilint777 — `jilint777_submission_20261004142740`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- Full bilingual conjecture read. Base metadata marks the ID unsolved; the PR adds only its own directory.
- Read the complete report and all six shipped PDF pages. Fresh two-pass `pdflatex` build exited 0; all pages rendered. Text differences are old bullet-glyph extraction artifacts only.
- Fresh self-contained Lean 4.19.0 project: `lake build` exited 0; direct warning-as-error Lean check exited 0.
- No forbidden proof shortcut. Principal theorems use at most `propext`, `Classical.choice`, and `Quot.sound`.
- Ran `verify.py` independently: exit 0; exact facet/edge computations, exhaustive cycle and path searches, all certificates, and all auxiliary checks passed.

## Counterexample

The rhombic dodecahedron

`R = conv{(±2,0,0),(0,±2,0),(0,0,±2),(±1,±1,±1)}`

is a full-dimensional 3-polytope with 14 vertices. Its 24 edges are exactly the incident pairs joining one of the eight cube vertices `(±1,±1,±1)` to one of the six axis vertices. Thus the eight cube vertices form an independent set. Since `8>14/2`, no Hamiltonian cycle can exist; equivalently, the graph is bipartite with unequal parts of sizes 8 and 6. There is not even a Hamiltonian path.

This directly refutes the conjecture's minimality clause: a dimension-3 polytope has a non-Hamiltonian graph. The submission additionally proves the conjecture's first clause by constructing the non-Hamiltonian pyramid over `R` in dimension 4.

Lean defines exposed vertices/edges, full-dimensional polytopes, Hamiltonian cycles, and the exact minimality statement. It proves all 24 rhombic-dodecahedron edges and 67 non-edges by explicit integer functionals/midpoint certificates, proves dimension 3 and non-Hamiltonicity, proves the 4D pyramid, and verifies non-vacuity with an octahedron Hamiltonian cycle. The integer-to-real rational-polytope bridge is mathematically sound. Python independently recomputes facets/edges and exhaustively searches both cycles and paths.

**Disposition: APPROVED.**
