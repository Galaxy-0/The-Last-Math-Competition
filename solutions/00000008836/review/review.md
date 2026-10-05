# Solution Review — Conjecture 00000008836 (PR 554)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004220000`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read in full from `conjectures/00000008836.md` (English + Chinese). No SOURCE.md is present; the submission instead ships `verification/original.md`, which is byte-identical (`diff` clean) to the official file.
- LaTeX report `proof.tex` read in full; independently rebuilt with `latexmk -pdf` (pdflatex) in a scratch directory — compiles with no errors. Text extracted from both the shipped Tectonic PDF and the rebuilt PDF with pypdf: whitespace-stripped text matches exactly; raw extraction differs only in kerning/hyphenation glyph artifacts ("W ork" vs "Work"), which is expected across engines.
- Fresh `lake build` on Lean v4.19.0 with Mathlib pinned at c44e0c8e (linked against the prebuilt pool): **Build completed successfully**, zero errors. Two harmless lint warnings (`unnecessarySeqFocus` at Main.lean:41, unused variable at Main.lean:117).
- Axiom audit: `#print axioms` run on all eight main theorems (`f_properties`, `mirror_properties`, `bregman_properties`, `maximal`, `unique_prox`, `zero_relative_error`, `not_convergent`, `not_weak`) — every one depends only on `[propext, Classical.choice, Quot.sound]`.
- Grep for `sorry`, `native_decide`, `axiom` declarations, `unsafe`, `@[implemented_by]`, `extern`, `admit` across the whole submission: no hits.
- Auxiliary code: none (only verification logs; `direct-search.json` is an empty result list). Nothing to execute.
- `metadata.csv` on main marks 00000008836 as neither proven nor disproven (unsolved).

## Semantic audit
The official text asserts, unconditionally: "Splitting under Bregman distances always converges; and the convergence criterion is summability of the decreasing distance sequence" (Bregman 距离下的分裂恒收敛). This is a conjunction whose first conjunct is a universal convergence claim with no solvability hypothesis. The submission disproves that first conjunct, which suffices to refute the conjecture as stated, and it explicitly scopes what it does not touch (the summability characterization and convergence theorems that assume a solution exists).

The counterexample is the cleanest possible one and it is mathematically correct. On the real Hilbert line with mirror h(x) = x²/2, the Bregman distance is exactly D_h(y,x) = (y−x)²/2. For the proper closed convex objective f(x) = −x (whose subdifferential is the constant singleton {−1}), the unit-penalty proximal subproblem min_y −y + (y−x)²/2 has first-order condition −1 + (y−x) = 0, hence the unique global minimizer y = x + 1; the gap identity Q_x(z) − Q_x(x+1) = (z−(x+1))²/2 makes uniqueness and existence rigorous. The iteration x_{k+1} = x_k + 1 gives x_k = x_0 + k, which diverges in norm for every start; since the identity is a continuous linear functional on ℝ, weak convergence fails too. I verified all of these computations independently (they are one-line calculus checks).

The Lean formalization is faithful rather than weakened. `Subgradient` is the genuine all-competitor inequality ∀z, v(z−x) ≤ f(z)−f(x) (not a pointwise derivative surrogate); `Prox` is the full argmin relation ∀z, Q_x(y) ≤ Q_x(z) (not first-order stationarity); `maximal` uses maximality by inclusion among monotone graphs and is actually proved; `RelativeError` is the standard Svaiter-type certificate ‖v + ∇h(y) − ∇h(x)‖² + 2e ≤ σ²‖∇h(y) − ∇h(x)‖² with e = 0, satisfied for every admissible σ since the residual −1 + (x+1) − x vanishes; and `not_convergent`/`not_weak` negate convergence for every candidate limit a and every starting point, exactly matching the strength needed against the "always converges" claim. Since the method is executed exactly (e = 0, exact inclusion), it is a legitimate zero-error instance of a relative-error Bregman method, so the counterexample lies inside the conjecture's stated scope. The minor definitional liberalities ("Proper" encoded as ∃x, h x < ⊤, real-valued functions anyway) do not weaken any decisive theorem.

The report and the Lean file agree theorem-by-theorem (properties of f and h, gradient, Bregman identity, subdifferential singleton, maximality, argmin relation, inclusion, zero residual, iterates, nonconvergence in norm and weakly, nonexistence of a minimizer). Consistency note: in this example the Bregman distances D_h(x_{k+1},x_k) = 1/2 are not summable, cohering with non-convergence rather than contradicting the untouched second conjunct.

## Issues found
None blocking. (Two non-fatal lint warnings in the Lean build; Tectonic-vs-pdflatex extraction artifacts in the PDF diff, content identical.)

## Verdict
APPROVED. The submission disproves the official conjecture's unconditional convergence claim with a fully verified, quantifier-faithful counterexample: an exact Bregman proximal relative-error splitting on f(x) = −x whose iterates provably diverge for every starting point. Every mechanical check (independent PDF rebuild and match, clean fresh build, standard-axioms-only audit, no forbidden constructs, unsolved metadata) passed, and the mathematics checks out end to end.
