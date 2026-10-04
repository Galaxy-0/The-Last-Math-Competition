# Solution Review — Conjecture 00000000377 (PR 495)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004154100`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff from the clean base adds only the correctly named personal submission folder. Base metadata marks conjecture 00000000377 unsolved. The copied bilingual `original-source.md` is byte-identical to `conjectures/00000000377.md`.
- **LaTeX and PDF.** I read the complete two-page report and every submitted source/config/log file. A fresh `latexmk -pdf` build succeeded (exit 0; 2 pages). I extracted text from the shipped and freshly built PDFs, normalized them, and rendered both fresh pages with Ghostscript. The report source and PDF content match; differences are compiler/spacing artifacts. No auxiliary numerical program is used.
- **Lean.** In a fresh copied project using the official shared pinned Mathlib tree, `lake build` completed successfully. Direct `lake env lean -DwarningAsError=true Main.lean` also exited 0. Six central axiom audits report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** The submitted Lean/config files contain no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `skipKernelTC`, or trust override. The only “axiom” occurrences are legitimate `#print axioms` audits.
- **Author logs.** The supplied Lean/PDF logs agree with my replay but were treated only as evidence, not as substitutes.

## Semantic audit

The first conjunct concerns parameters on the Mandelbrot boundary for which a parabolic periodic point has a Liouville multiplier. In complex dynamics, “parabolic” (rationally indifferent) means that the multiplier is a root of unity; multiplier `1` is the special convention also covered. Thus if the multiplier is `λ` and the point has positive period `n`, there is `q>0` with `λ^q=1`.

Lean encodes the actual quadratic family by the polynomials `z²+c` and their composition iterates. It proves that polynomial evaluation agrees with function iteration and defines the multiplier as the actual complex derivative, with a proved bridge to polynomial derivative evaluation. Periodicity, positive period, and the root-of-unity multiplier condition are explicit. The Mandelbrot set is the actual bounded-critical-orbit set, and the parameter set uses its frontier.

A real Liouville number is necessarily irrational. If such a number `ξ` were a real root of unity, then `ξ^q=1` implies `|ξ|=1`, and the only real possibilities are `ξ=1` or `ξ=-1`, both rational—a contradiction. Therefore no parabolic multiplier can be a real Liouville number. Since the obstruction already holds for every parameter before restricting to the Mandelbrot boundary, imposing that boundary condition—and any further Julia-set restriction—still leaves the empty set. Mathlib's Hausdorff dimension of the empty set is `0`, not the conjectured `1`.

The Lean parameter predicate requires membership in `frontier mandelbrot`, a positive-period parabolic point, a real Liouville multiplier, and equality with the actual multiplier. It proves `parameters = ∅`, `dimH parameters = 0`, and `dimH parameters ≠ 1`. This is non-vacuous in the relevant sense: it uses the actual dynamics and standard definitions, and shows the claimed dimension-1 set cannot exist.

Only the Liouville dimension conjunct is refuted. The separate badly-approximable/full-dimensional clause is not needed to disprove the conjunction and is not overclaimed.

## Verdict rationale

The mathematical obstruction is decisive and elementary: roots of unity are algebraic/rational when real, while Liouville numbers are irrational. The formal objects and theorem correspond directly to the official first claim. Fresh PDF/Lean builds, strict replay, standard-only axiom audits, and source scans all pass.

## Disposition

APPROVED — ready for merge (PR 495). No merge action was taken by this reviewer.
