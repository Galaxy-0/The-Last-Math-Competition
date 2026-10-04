# Solution Review — Conjecture 00000008487 (PR 500)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004162800`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff from clean base adds only the correctly named personal submission folder. Base metadata marks conjecture 00000008487 unsolved. The included original-conjecture copy matches the official bilingual file exactly.
- **LaTeX and PDF.** I read the complete one-page report and every submitted source/config/verification file. Fresh `latexmk -pdf` compilation succeeded (exit 0; 1 page). I extracted, normalized, and compared shipped/fresh text and rendered the fresh page. No auxiliary numerical program is used.
- **Lean.** Using the official shared pinned Mathlib tree, `lake build` completed successfully. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0. Four central axiom audits report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No proof escape, custom axiom, unsafe declaration, implementation override, native decision shortcut, or kernel-trust override occurs.

## Semantic audit

The conjecture simultaneously asserts that the locked-function set `L` is dense and that its complement `Y\L` is a dense open set. These conditions are inconsistent in every nonempty topological space.

Indeed, if `L` is dense and `Y\L` is open and nonempty, density forces `L` to meet the nonempty open set `Y\L`, giving `L∩(Y\L)≠∅`, impossible. Equivalently, an open complement of a dense set must be empty, and the empty set is not dense in a nonempty space. This does not require Baire category, measure, dimension, or the additional `Gδ` condition. Lean proves the universal impossibility using Mathlib's actual `Dense` and `IsOpen` predicates.

The relevant function space `Y=C([0,1],ℝ)` with its usual topology is nonempty (it contains the zero observable). The universal obstruction applies to every subset of this space, hence to the actual locked-function set under any possible locking convention. Lean includes `IsGδ L` in the claimed conjunction and proves that no candidate set can satisfy all four asserted topological conditions.

This logical inconsistency refutes the conjecture as stated without needing to interpret locking, infinite-dimensional Lebesgue measure, box dimension, or logarithmic gaps. The report correctly notes that a dense `Gδ` set can have a dense complement; the special contradiction comes from requiring that complement to be open.

## Verdict rationale

The two density/topology clauses of the official statement are formally contradictory. The Lean theorem proves this universally and specializes to the actual nonempty interval-observable space. All builds, strict replay, axiom audits, scans, and PDF checks pass.

## Disposition

APPROVED — ready for merge (PR 500). No merge action was taken by this reviewer.
