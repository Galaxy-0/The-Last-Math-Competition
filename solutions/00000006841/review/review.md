# Solution Review — Conjecture 00000006841 (PR 436)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004061016`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** The official statement concerns subspace reflection operators and their combinations being unitary isometries. The report interprets “combination” as composition, the standard mathematical reading, and proves each reflection and every finite composition is a surjective linear inner-product isometry.
- **Repository structure.** PR head `b337a09a...`, from clean base `4cc82278...`, adds only its correctly named folder. Base metadata has no prior solve.
- **LaTeX/PDF.** Read the full report and both shipped pages. Independently compiled twice; both passes exited 0. Ghostscript rendering succeeded and fresh/shipped content matches.
- **Lean.** Used the shared pinned Lean 4.19/Mathlib setup, ran `lake build` (exit 0), and replayed `Main.lean` with warnings as errors (exit 0). All five principal audits use only standard axioms.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, `implemented_by`, or `skipKernelTC`.
- **Auxiliary code.** None needed.

## Semantic audit

For `x=u+v` with `u∈K` and `v∈K⊥`, the orthogonal reflection is `u−v`. Squaring gives `x`, so the map is bijective; it fixes exactly `K` and negates `K⊥`. Vanishing cross inner products imply preservation of every inner product and hence every distance. Compositions of surjective linear isometries retain these properties, with the empty composition equal to identity.

Lean formalizes this through Mathlib's actual orthogonal projection and reflection equivalence. Its `UnitaryIsometry` predicate explicitly includes linearity, surjectivity, metric isometry, and inner-product preservation. Arbitrary finite lists are composed through genuine equivalences, and closed subspaces of complete spaces receive their required projection without assuming it. Coverage includes real and complex Hilbert spaces, projectable subspaces, closed subspaces, finite compositions, and the two-reflection case.

## Issues found

None blocking.

## Verdict rationale

The standard orthogonal reflection theorem is correct and is faithfully formalized at the required level of generality. Independent PDF, Lean, axiom, and semantic checks pass.

## Disposition

**APPROVED**
