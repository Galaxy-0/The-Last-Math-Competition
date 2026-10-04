# Solution Review — Conjecture 00000008839 (PR 393)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004040754`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The Yosida approximation error is always λ times the operator norm; and the convergence of approximate solutions is first order as λ → 0" (disproof submission).
- LaTeX: pdflatex twice, exit 0 both passes, 0 errors; shipped report.pdf is a genuine 2-page PDF whose extracted text matches report.tex (title, author, sections verified).
- Lean build: `lake build` exit 0, "Build completed successfully", no warnings; six `#print axioms` lines all show only [propext, Classical.choice, Quot.sound].
- Forbidden content: grep over lean/Main.lean and lakefile.lean for sorry/admit/native_decide/axiom decls/unsafe/implemented_by/extern/skipKernelTC — no hits. Recorded verification/lean-build.txt and lean-check.txt match my independently reproduced build output exactly.
- Auxiliary code: no scripts; verification/ evidence files (lean-build.txt, lean-check.txt, pdf-build.txt, eligibility.txt, source.md) all present and consistent; source.md reproduces the bilingual conjecture verbatim. Hand-recomputation: (I+¼·4id)=2id ⇒ J_λ=½I ⇒ A_λ=4(I−½I)=2id ⇒ ‖A−A_λ‖=2 > λ‖A‖=(¼)(4)=1 — matches the Lean-computed values.
## Semantic audit
Conjecture literal claim (EN): "The Yosida approximation error is always lambda times the operator norm." The submission refutes the universally quantified first conjunct (refuting a conjunct refutes the conjunction); the second clause (first-order convergence of approximate solutions) is explicitly left untouched — unnecessary for the disproof.

Lean encodings (namespace `YosidaCounterexample`):
- `def yosida (R : ℝ →L[ℝ] ℝ) (l : ℝ) := l⁻¹ • (ContinuousLinearMap.id ℝ ℝ - R)` — the standard Yosida approximation A_λ = λ⁻¹(I − J_λ).
- The resolvent is not assumed: `theorem resolvent_left : J.comp (shifted A lambda) = ContinuousLinearMap.id ℝ ℝ` and `theorem resolvent_right : (shifted A lambda).comp J = ContinuousLinearMap.id ℝ ℝ` prove J = (I+λA)⁻¹ by genuine two-sided inverse identities (shifted A lambda x = 2*x by norm_num/ring).
- Norms are computed, not assumed: `theorem scalarMap_norm (a : ℝ) : ‖scalarMap a‖ = |a|` via opNorm_le_bound plus evaluation at the unit vector; `theorem actual_norms : ‖A‖ = 4 ∧ ‖A-approximation‖ = 2`.
- Admissibility of the operator: `theorem A_monotone` (4(x−y)² ≥ 0) and `theorem A_maximal_monotone` via the standard graph-extension definition `MaximalMonotone T := MonotoneOperator T ∧ ∀ B, MonotoneOperator B → (∀ x, T x ⊆ B x) → ∀ x, B x ⊆ T x` — the y = x + v/8, v = u−4x argument (0 ≤ −v²/16 ⇒ v = 0) is the correct Minty-style maximality proof.

Final theorem: `theorem conjecture_00000008839_error_false : MaximalMonotone (graphOperator A) ∧ 0 < lambda ∧ J.comp (shifted A lambda) = id ∧ (shifted A lambda).comp J = id ∧ approximation = yosida J lambda ∧ ¬ (‖A-approximation‖ ≤ lambda*‖A‖)`.

Readings audit: as equality ‖A−A_λ‖ = λ‖A‖: 2 ≠ 1, false. As an upper bound ‖A−A_λ‖ ≤ λ‖A‖: 2 > 1, false (this is what the theorem literally negates, the stronger disproof). Pointwise on the unit vector: `unit_vector_error : ‖A 1 - approximation 1‖ = 2 ∧ lambda*‖A‖ = 1`, also false. Alternative "operator norm" readings (‖A_λ‖ = 2 ⇒ λ‖A_λ‖ = ½; ‖J_λ‖ = ½ ⇒ λ‖J_λ‖ = ⅛) all fail to equal 2 as well. Not vacuous: λ > 0, A maximal monotone (the customary Yosida setting), resolvent exists everywhere as a two-sided inverse. The counterexample is decisive under every reasonable interpretation of the clause.
## Issues found
none blocking
## Verdict rationale
The Lean project compiles cleanly with only standard axioms, computes the resolvent and norms from first principles (no assumed scalar data), and establishes a genuine maximal-monotone counterexample in which ‖A−A_λ‖ = 2 strictly exceeds λ‖A‖ = 1, refuting the literal "always λ times the operator norm" clause under equality, upper-bound, and pointwise readings. The report faithfully reproduces the conjecture and the construction, compiles to a matching PDF, and all recorded verification evidence matches independent reproduction.

## Disposition
APPROVED — merged into main (PR 393). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
