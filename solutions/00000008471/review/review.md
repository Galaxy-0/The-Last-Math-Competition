# Solution Review — Conjecture 00000008471 (PR 499)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004161500`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff from clean base adds only the correctly named personal submission folder. Base metadata marks conjecture 00000008471 unsolved. The included original-conjecture copy is byte-identical to `conjectures/00000008471.md`.
- **LaTeX and PDF.** I read the complete one-page report and every submitted source/config/verification file. Fresh `latexmk -pdf` compilation succeeded (exit 0; 1 page). Text extraction, normalized comparison, and Ghostscript rendering confirmed agreement. No auxiliary numerical program is used.
- **Lean.** Using the official shared pinned Mathlib tree, `lake build` completed successfully. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0. Six central axiom audits report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No proof escape, custom axiom, unsafe declaration, implementation override, native decision shortcut, or kernel-trust override occurs.

## Semantic audit

The final official clause says the complement of the locked continuous observables is dense. Neither language excludes singleton dynamical systems.

Let `X={a}` with the identity map. The only probability measure is `δ_a`: the whole singleton space has probability one, and it is the only nontrivial measurable set. This measure is invariant. For every continuous observable `f`, its integral is `f(a)`, so over all invariant probability measures the unique maximizing measure is `δ_a`. Lean proves the full measure classification, invariance, Bochner integral, and maximizing-measure equivalence rather than choosing from a restricted list.

The point `a` has period one, and equidistribution on its orbit is `(1/1)∑_{j=0}^{0}δ_{T^j a}=δ_a`. Therefore every continuous observable is locked in the explicit sense stated by the conjecture: its entire maximizing-measure set consists of an equidistribution on a finite periodic orbit. Lean defines the actual weighted orbit measure and proves both periodicity and locking for every observable.

Thus the locked-function set is all of the nonempty continuous-function space `C(X,ℝ)`. Its complement is empty, hence open but not dense. This directly falsifies the “dense open complement” clause. The report also notes that the example is stable under every perturbation, since the unique invariant probability measure remains the same, so adding a perturbation-persistence requirement would not rescue the claimed density.

The submission limits itself to the final clause; it does not dispute the separate generic-locking statement or the atom-count clause.

## Verdict rationale

This is a valid literal singleton-system counterexample. The formalization proves all actual measure-theoretic and dynamical objects and the exact non-density predicate. Builds, strict replay, standard-only audits, source scans, and PDF verification all pass.

## Disposition

APPROVED — ready for merge (PR 499). No merge action was taken by this reviewer.
