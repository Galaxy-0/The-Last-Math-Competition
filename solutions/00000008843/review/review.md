# Solution Review — Conjecture 00000008843 (PR 385)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004032842`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The subdifferential of f is always maximal monotone; the equality characterization is cyclic monotonicity, and closed convex functions are uniquely determined by their subdifferentials" (CN: 闭凸函数被次微分唯一决定, with no "up to additive constant" qualification in either language).
- LaTeX: recompiled in /tmp/tlmc-review5/scratch/pr-385 with pdflatex twice, exit 0, zero errors; shipped report.pdf is a genuine PDF (37,443 bytes, tectonic, CID fonts) consistent with report.tex (title "Subdifferentials forget additive constants / Conjecture 00000008843"); full report read — it gives the subgradient definition, closedness/convexity of constants, the ∂h_c(x) = {0} computation, the general additive-constant invariance, and the formal correspondence.
- Lean build: `lake build` exit 0 ("Build completed successfully", 1469 targets — identical count to the submitter's lean-build.txt; ~450 missing Mathlib oleans were source-compiled due to the environment's pruned cache). Zero warnings. `#print axioms` for all four audited theorems: [propext, Classical.choice, Quot.sound] only.
- Forbidden content: grep for `sorry`, `admit`, `native_decide`, `axiom `, `unsafe`, `implemented_by`, `extern`, `skipKernelTC` over Main.lean — no matches; no custom axioms.
- Auxiliary code: none shipped, none needed (symbolic proof over ℝ). My own independent Python check confirmed: ∂(constant c)(x) = {0} for c ∈ {0, 1, −3.7} (numeric sweep over v and y), ∂(x²+1)(x) = ∂(x²)(x) = {2x} (additive invariance), and f≡0 ≠ g≡1 — exactly the Lean content.
## Semantic audit
Conjecture literal claim (third conjunct): "closed convex functions are uniquely determined by their subdifferentials." Formalized negated statement:

```lean
def Subgradient (f : ℝ → ℝ) (x v : ℝ) : Prop := ∀ y : ℝ, f x + v * (y-x) ≤ f y
def subdifferential (f : ℝ → ℝ) (x : ℝ) : Set ℝ := {v | Subgradient f x v}
def epigraph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | f p.1 ≤ p.2}
def ClosedConvex (f : ℝ → ℝ) : Prop := ConvexOn ℝ Set.univ f ∧ IsClosed (epigraph f)
def UniqueDetermination : Prop := ∀ f g : ℝ → ℝ,
  ClosedConvex f → ClosedConvex g → (∀ x, subdifferential f x = subdifferential g x) → f = g
theorem conjecture_00000008843_false : ¬ UniqueDetermination
```

(i) Definitional faithfulness: `Subgradient` is the standard global supporting-inequality definition of the subdifferential in one dimension (dual of ℝ identified with ℝ); `epigraph` = {(x,t) : f(x) ≤ t} is the standard epigraph; `ClosedConvex` = Mathlib `ConvexOn` on the whole line plus closed epigraph — the standard notion of a (proper, finite) closed convex function. (ii) Hypotheses: witnesses f ≡ 0 and g ≡ 1 are proved `ClosedConvex` (`constant_closed_convex`, via `convexOn_const` and closedness of {c ≤ t} via `isClosed_le`); their subdifferentials are proved equal at every point (`identical_subdifferentials`, through `constant_subdifferential : subdifferential (constant c) x = {0}`, which derives v = 0 from the defining inequality at y = x±1 with `nlinarith`); distinctness by evaluation at 0 (`functions_distinct`). (iii) The final theorem is the formal negation of the literal universal uniqueness statement, so the submission refutes the conjecture. (iv) Not vacuous and not a numeric-facts-only proof: the general theorem `additive_constant_invariance (f : ℝ → ℝ) (c x : ℝ) : subdifferential (fun y => f y + c) x = subdifferential f x` shows the non-uniqueness mechanism (∂ forgets additive constants) holds for ALL real functions, so the counterexample is intrinsic to the definition rather than a degenerate corner case; constant functions are bona fide closed convex functions and the conjecture text carries no normalization excluding them.

Scope honesty: the first two conjuncts (maximal monotonicity; cyclic-monotonicity characterization — both true theorems of Rockafellar) are explicitly not addressed; a conjunction is disproved by refuting one conjunct, and both the report and README state this precisely.
## Issues found
- Minor (non-blocking): the counterexample uses constant functions — the most elementary closed convex pair; acceptable since the literal statement has no "up to additive constant" or normalization clause, and the general invariance theorem is included. Flagged for awareness only.
- Minor (non-blocking): README "Reproduce" mentions `lake exe cache get`; unnecessary with pinned manifest; verified by direct `lake build`.
## Verdict rationale
The submission proves, with faithful standard definitions of subdifferential and closed convex function, that the distinct closed convex functions f ≡ 0 and g ≡ 1 have identical subdifferentials at every real point, and proves the general fact that adding a constant never changes the subdifferential; the final theorem formally negates the conjecture's universal uniqueness clause as literally stated in both languages. Build is clean with only standard axioms, the LaTeX compiles and matches the shipped PDF, and my independent numeric checks reproduce the subdifferential computations.

## Disposition
APPROVED — merged into main (PR 385). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
