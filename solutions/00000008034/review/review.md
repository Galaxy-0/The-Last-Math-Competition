# Solution Review — Conjecture 00000008034 (PR 498)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004154900`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff from clean base adds only the correctly named personal submission folder. Base metadata marks conjecture 00000008034 unsolved. The report clearly identifies the unrestricted global solution-graph interpretation being addressed.
- **LaTeX and PDF.** I read the complete one-page report and every submitted source/config file. Fresh `latexmk -pdf` compilation succeeded (exit 0; 1 page). I extracted and compared shipped/fresh text and rendered the fresh page with Ghostscript. The normalized text is effectively identical. No auxiliary numerical program is used or required.
- **Lean.** Using the official shared pinned Mathlib tree, `lake build` completed successfully with no warnings. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0. Eight central axiom audits report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No proof escape, custom axiom, unsafe declaration, implementation override, native decision shortcut, or kernel-trust override occurs. The words “axioms” in source comments/audits are explanatory or legitimate `#print axioms` commands.

## Semantic audit

The official definition asks for an o-minimal closure of solution sets of differential polynomial systems over `ℝ`, without a bounded-domain or nonoscillation restriction. Its explicit reference to including genuine solutions of `x'=x` supports the submission's global solution-graph reading.

The real sine function is smooth and globally satisfies the polynomial differential equation

`y'' + y = 0`

(equivalently, the polynomial first-order system `y'=z`, `z'=-y`). Therefore the proposed closure must contain its graph `G={(t,sin t)}`. Lean verifies the actual second derivative identity rather than treating sine as an abstract formal symbol.

If an o-minimal expansion of the real field contains `G`, intersecting with the horizontal zero line and projecting to the first coordinate defines the zero set of sine:

`Z={t∈ℝ : sin t=0}=πℤ`.

Lean proves this exact intersection/projection identity. The set `πℤ` is infinite, but every order-connected subset contained in it has at most one point: between any two consecutive integer multiples of `π`, the midpoint has nonzero sine. Thus no finite union of points/intervals—or, more generally, order-connected sets—can equal `Z`. This violates the unary o-minimality property.

The Lean interface is intentionally unbundled: it assumes only unary/binary definable families, closure under this zero-fiber operation, and the necessary unary o-minimality condition. Every actual o-minimal real-field structure satisfies these requirements, so proving that they are incompatible with containing `G` rules out every such structure. The submission is transparent that this is not a bundled Mathlib model-theory structure and does not overclaim a formalization of all definability operations.

Since the proposed minimal structure cannot exist under the stated unrestricted closure, its later extension/conservativity and counting-exchange claims cannot rescue it. The report also accurately limits the result: a closure restricted to bounded or nonoscillatory solutions would be a different, additional hypothesis absent from the source.

## Verdict rationale

Sine supplies the standard obstruction to o-minimality: a polynomial ODE solution with infinitely many isolated zeros. The formal proof verifies the differential equation, zero characterization, infinitude, order-connected obstruction, and zero-fiber projection. All independent builds, strict replay, audits, scans, and PDF checks pass.

## Disposition

APPROVED — ready for merge (PR 498). No merge action was taken by this reviewer.
