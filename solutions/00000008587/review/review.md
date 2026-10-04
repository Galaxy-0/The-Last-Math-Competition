# Solution Review — Conjecture 00000008587 (PR 413)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004052845`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- Full bilingual conjecture read. Base metadata marks it unsolved. The PR adds only its own submission directory.
- Full report and both shipped PDF pages read. Fresh two-pass `pdflatex` build exited 0; both pages rendered. Rebuilt PDF content agrees up to compiler text-extraction artifacts.
- Full Lean 4.19.0/Mathlib build at pinned revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`: `lake build` exited 0 (`[2793/2794] Built Main`); direct warning-as-error check exited 0.
- No forbidden proof shortcut. All principal theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- No auxiliary computation is needed.

## Counterexample

Take the faithful unital commutative scalar operator algebra

`A={aI : a∈ℂ}`

acting on the fixed representation space `H=ℂ³`.

Relative to every vector-space basis of `H`, each represented operator `aI` has matrix `aI`, hence is diagonal (in particular upper triangular). Thus a triangularizing representation basis exists. But `H` has complex vector-space dimension 3, so every basis has exactly three elements. The minimum size is therefore 3, not at most 2.

Lean formalizes the actual algebra map `Algebra.ofId`, its range subalgebra, faithfulness, unit, commutativity, continuity, arbitrary-basis matrix representation, upper-triangularity, and universal basis cardinality 3. It proves no representation basis has cardinality at most 2. This directly refutes the explicit double-dimension upper-bound clause.

**Disposition: APPROVED.**
