# Solution Review — Conjecture 00000008232 (PR 406)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004045232`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — vertex-count law: "the number of vertices of the core of convex geometry (anti-convex games) is 2^{n-1}" (part of a 4-conjunct Shapley/coalition-structure conjecture)
- LaTeX: proof.tex recompiled in /tmp/tlmc-review5/scratch/pr-406 with pdflatex (2 passes), exit 0, 0 errors, 2 pages; shipped proof.pdf is a real PDF 1.5; verification/ logs (checks.txt, eligibility.txt, tectonic.log, pdf-qa.txt) consistent with my reproduction
- Lean build: exit 0 ("Build completed successfully", 2795 jobs); only output is 5 `#print axioms` info lines — [propext, Classical.choice, Quot.sound] (geometry theorem even subset: no choice)
- Forbidden content: grep over own Main.lean for sorry/admit/native_decide/`axiom `/unsafe/implemented_by/extern/skipKernelTC: no hits; verification/checks.txt records the same audit
- Auxiliary code: no scripts (checks.txt: "no auxiliary computations are needed" — confirmed); independent python3 re-derivation: payoff core = {(1,1)} forced by x₀≥1, x₁≥1, x₀+x₁=2; cost core identical; singleton has exactly 1 extreme point; 2^{2-1}=2≠1; more generally additive games have singleton cores so the law fails for every n≥2
## Semantic audit
Conjecture literal clause (EN): "the number of vertices of the core of convex geometry (anti-convex games) is 2^{n-1} (a vertex count law)". The submission refutes this conjunct, which suffices for the conjunction.

Lean encoding:
- `abbrev Player := Fin 2`, `Coalition := Finset Player`, `Allocation := Player → ℝ`.
- `def IsConvexGeometry (cl) : Prop := cl ∅ = ∅ ∧ extensive ∧ monotone ∧ idempotent ∧ anti-exchange` — the standard closure-operator definition of a finite convex geometry; `theorem boolean_convex_geometry : IsConvexGeometry closure` proves it for the identity closure on the full Boolean family (anti-exchange holds vacuously; proof is exactly this argument).
- `Feasible s := closure s = s` with `every_coalition_feasible` and `feasible_accessible` — feasible-family convention covered.
- `def game (s) : ℝ := s.card`; `game_modular` via Mathlib's `card_union_add_card_inter`; `game_supermodular`/`game_submodular` both hold with equality — so the game satisfies BOTH the convex-game and the "anti-convex" (submodular/cost) non-strict inequalities.
- `payoffCore := {x | (∑ i, x i) = game univ ∧ ∀ s, Feasible s → game s ≤ ∑ i ∈ s, x i}` and `costCore` with reversed inequality — the standard core definitions with efficiency plus EVERY feasible-coalition inequality (not just singletons).
- `payoff_core_singleton : payoffCore = {ones}` and `cost_core_singleton : costCore = {ones}` — full cores computed exactly, both conventions, both directions.
- `payoff_extreme_points : payoffCore.extremePoints ℝ = {ones}` via Mathlib's actual `Set.extremePoints` (open-segment definition), `extremePoints_singleton`.
- Final `vertex_count_fails : (payoffCore.extremePoints ℝ).ncard = 1 ∧ (costCore.extremePoints ℝ).ncard = 1 ∧ ... ≠ 2 ^ (Fintype.card Player - 1)` — actual cardinalities: 1 ≠ 2^{2-1} = 2.

Hypotheses: the conjecture's "anti-convex games" is undefined in both source languages; under the standard non-strict definitions of convex/supermodular and anti-convex/submodular games on convex geometries, this modular game is in the class (both inequalities hold), and the full Boolean family is a genuine (simplest) finite convex geometry. Not vacuous: the core is a genuine zero-dimensional polytope whose unique vertex is counted with Mathlib's extreme-point machinery, and 1 ≠ 2 is a hard contradiction of the count law.
## Issues found
none blocking. FLAG for coordinator attention: (a) the game is additive/modular — a boundary member of both the convex and anti-convex classes (satisfies both non-strict inequalities with equality); if "anti-convex" were intended strictly (strictly submodular) the example would be out of class, but the source text nowhere defines or restricts this, and the submission discusses the ambiguity openly and satisfies both conventions; (b) the convex geometry is the trivial one (identity closure on 2^N) — again permitted, being the simplest genuine convex geometry. Under the repo's literal-statement precedent both are acceptable.
## Verdict rationale
The Lean project proves, with genuine Mathlib convex-geometry, core and extreme-point definitions, that the additive normalized two-player game on the full Boolean convex geometry has core exactly {(1,1)} under both payoff and cost conventions, hence exactly one core vertex versus the conjectured 2^{n-1}=2 — a clean contradiction of the vertex-count law. Build is clean with only standard axioms, the PDF matches, and the arithmetic is independently confirmed. The only caveats are the disclosed class-boundary choices, which the unrestricted source text permits.

## Disposition
APPROVED — merged into main (PR 406). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
