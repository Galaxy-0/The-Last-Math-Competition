# Solution Review — Conjecture 00000007164 (PR 501)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004155247`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff from clean base adds only the correctly named personal submission folder. Base metadata marks conjecture 00000007164 unsolved. The report accurately quotes the unrestricted maximal-radius claim.
- **LaTeX and PDF.** I read the complete two-page report and all submitted source/config files. Fresh `latexmk -pdf` compilation succeeded (exit 0; 2 pages). I extracted and compared shipped/fresh text and rendered both fresh pages. No auxiliary numerical program is used.
- **Lean.** Using the official shared pinned Mathlib tree, `lake build` completed successfully. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0. Eight central axiom audits report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No proof escape, custom axiom, unsafe declaration, implementation override, native decision shortcut, or kernel-trust override occurs.

## Semantic audit

The official statement says “the maximal radius graph is the star” without restricting to trees or fixing the number of edges. The submission compares two connected simple graphs on the same three vertices: the star `K₁,₂` with edges `{0,1}` and `{0,2}`, and the triangle `K₃`, which additionally has edge `{1,2}`.

Their complex adjacency matrices have complete spectra

`σ(K₁,₂)={0,√2,-√2}`, `σ(K₃)={2,-1}`.

Lean derives these from the actual `SimpleGraph.adjMatrix`, determinant invertibility, and full determinant identities, rather than assuming eigenvalue certificates. Consequently the spectral radii are `√2` and `2`, with `√2<2`. Thus even with the vertex count fixed at three, the star does not maximize adjacency spectral radius among simple connected graphs. A fortiori it cannot be the unrestricted maximal-radius graph asserted by the conjecture.

The submission explicitly does not claim to refute a different fixed-edge/tree-only extremal theorem; such restrictions are absent from the official statement. Refuting the first conjunct suffices without interpreting the separate neighborhood clause.

## Verdict rationale

The counterexample is elementary and exactly computed. Lean constructs both actual graphs, proves connectivity and edge counts, computes full spectra and radii, and directly negates the same-three-vertex maximality predicate. All builds, strict replay, audits, scans, and PDF checks pass.

## Disposition

APPROVED — ready for merge (PR 501). No merge action was taken by this reviewer.
