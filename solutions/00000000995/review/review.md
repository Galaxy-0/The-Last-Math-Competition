# Solution Review — Conjecture 00000000995 (PR 574)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004210000`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read (`conjectures/00000000995.md`): fixed-point existence for set-valued nonexpansive maps is claimed to hold on hyperconvex metric spaces, with a separate non-extension clause for general complete spaces. Neither language version states a boundedness hypothesis. The shipped `verification/original.md` is byte-identical to the official conjecture file. No top-level `SOURCE.md` (absent, not required). Metadata marks the conjecture unsolved (`proven=false`, `disproven=false`).
- LaTeX report (`proof.tex`) read in full; independent `latexmk -pdf` rebuild succeeded; extracted text of the shipped `proof.pdf` and the rebuild match exactly after NFKC/whitespace normalization (no glyph artifacts at all in this one).
- Fresh `lake build` on Lean toolchain v4.19.0 with Mathlib pinned at `c44e0c8ee63ca166450922a373c7409c5d26b00b` completed successfully (2794 targets), zero warnings, zero errors.
- `#print axioms` in the shipped `Main.lean` covers all seven audited theorems (hyperconvexity of ℝ, regularity of values, Hausdorff distance identity, no fixed point, exact orbit, divergence, and the combined counterexample theorem): every one depends only on `propext`, `Classical.choice`, `Quot.sound`.
- No auxiliary code shipped (`aux_code: none`); the mathematics is elementary and was verified directly.
- Grep audit clean: no `sorry`, `native_decide`, declared `axiom`, `unsafe`, `@[implemented_by`, `extern`, or `admit`.

## Semantic audit
The conjecture's first conjunct asserts that set-valued nonexpansive maps on hyperconvex metric spaces have fixed points, with no boundedness restriction in either the English or the Chinese text. The classical theorems (Aronszajn–Panitchpakdi for single-valued maps, Khamsi for set-valued maps) all require boundedness of the space, and the submission exhibits exactly the canonical obstruction: the real line with its usual metric is hyperconvex — Lean proves the full definition, namely that for an arbitrary indexed family of centers and nonnegative radii with |x_i − x_j| ≤ r_i + r_j for all i, j, the closed balls have a common point, by taking y = sup_i(x_i − r_i), which is nonempty-bounded-above by compatibility and satisfies |y − x_j| ≤ r_j for every j — and ℝ is unbounded.

On this space the set-valued map T(x) = {x+1} takes nonempty, closed, bounded, convex (singleton, hence compact and even hyperconvex) values; the Hausdorff distance identity hausdorffDist(T x, T y) = dist(x+1, y+1) = dist(x, y) is proved in Lean, so T is nonexpansive in the standard set-valued Hausdorff sense — and being singleton-valued, it simultaneously satisfies the single-valued nonexpansiveness definition and any weaker selection-distance variant, so no reasonable reading of "set-valued nonexpansive" escapes the counterexample. A fixed point would require x ∈ {x+1}, i.e. x = x+1, which is impossible; the fixed-point set is empty. The unique selection f(x) = x+1 has orbit fⁿ(0) = n (proved by induction as actual function iterates) tending to +∞, which explicitly displays the missing bounded-orbit hypothesis and confirms that the counterexample does not contradict the boundedness-qualified fixed-point theorems.

The quantifier structure matches the official text: the conjecture asserts an unqualified existence property on hyperconvex spaces; the disproof gives one hyperconvex space (with completeness also proved) and one map satisfying every stated hypothesis (set-valued, nonexpansive, nonempty closed bounded convex values) whose fixed-point set is empty. Since the conjunction's first conjunct is false, the conjecture as a whole is refuted; the report correctly leaves the separate (true) non-extension clause unused rather than making claims about it. The Lean formalization is honest throughout: hyperconvexity is proved from the raw ball-intersection definition rather than assumed as a certificate, the Hausdorff distance is Mathlib's genuine `hausdorffDist`, and the no-fixed-point conclusion follows from the defining membership, not from a restated equation.

## Issues found
None blocking.

## Verdict
APPROVED. The counterexample is mathematically correct and canonical — an unbounded hyperconvex space (ℝ, proved hyperconvex from the full arbitrary-family definition) carrying a Hausdorff-nonexpansive singleton-valued map with compact convex values and no fixed point — and it refutes exactly the unbounded hyperconvex existence clause asserted by the official bilingual conjecture while satisfying every hypothesis that text states. The Lean project is faithful and complete, builds with zero warnings on the pinned toolchain, uses only the three standard foundational axioms, and the shipped PDF matches an independent rebuild exactly.
