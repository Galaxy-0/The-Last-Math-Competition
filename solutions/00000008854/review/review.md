# Solution Review — Conjecture 00000008854 (PR 487)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004151447`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — the metric-matrix spectral midpoint is claimed optimal; a standard metric projected-gradient instance refutes it.
- Eligibility: base metadata is unsolved; the PR adds only its own properly named directory.
- LaTeX: independent build exit 0, two A4 pages, no substantive warnings; shipped/fresh content matches.
- Lean: shared official pinned dependencies linked; `lake build` exit 0 and default direct elaboration exit 0. Warnings-as-errors mode is defeated only by two non-substantive style-linter warnings, not a proof error.
- Axioms: only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none.
- Auxiliary programs: none needed.

## Semantic audit

Use `C=R`, identity metric `H=[1]`, and `f(x)=2x²`. The metric spectrum is `{1}`, hence the conjectured midpoint step is `1`; the projection is the identity. Since `∇f(x)=4x`, the update is `G_η(x)=(1-4η)x`. From `x_0=1`, the midpoint orbit is `(-3)^n` and its error diverges to infinity. Step `1/4` maps every point to the unique minimizer immediately. Lean proves the full eigenvalue set, global projection and uniqueness, gradient, unique minimum, update, all iterates, midpoint divergence, and that `|1-4η|` is uniquely minimized at `1/4`. This distinguishes the metric spectrum from the objective Hessian spectrum and decisively falsifies the metric-midpoint optimality clause.

## Verdict

APPROVED — the counterexample is concrete, formally faithful, and independently reproducible; the only direct-command issue is a non-substantive linter style warning.
