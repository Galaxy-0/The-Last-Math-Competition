# Solution Review — Conjecture 00000008850 (PR 391)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004035726`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — four-clause conjunction about the variational inclusion 0 ∈ A(x) + λx − p; the clause under attack: "single-valued continuity holds if and only if A is strongly monotone and the parameter domain is connected". Claimed and delivered as a DISPROOF (of the equivalence clause).
- LaTeX: pdflatex compiled twice, exit 0; shipped 2-page report.pdf genuine; text matches my rebuild modulo Tectonic-vs-pdflatex fraction/spacing extraction artifacts.
- Lean build: exit 0 (1514/1515 Built Main). No warnings. Six `#print axioms` lines (zero_inclusion_iff, solution_continuous, domain_connected, zero_maximal_monotone, counterexample, conjecture_00000008850_equivalence_false) = exactly [propext, Classical.choice, Quot.sound].
- Forbidden content: grep over Main.lean + lakefile.lean: no hits.
- Auxiliary code: verification/ records (lean-build.txt, lean-check.txt, pdf-build.txt, source.md, eligibility.txt) match my live results; source.md reproduces the bilingual conjecture verbatim. No numeric scripts needed; I re-verified the mathematics by hand (below). Toolchain Lean 4.19.0, Mathlib c44e0c8e….
## Semantic audit
Conjecture clause (EN/CN agree): 单值连续当且仅当 A 强单调且参数域为连通. The submission instantiates the literal objects of the definition:
- `def Solution A z x := ∃ u ∈ A x, u + z.2 * x - z.1 = 0` — exact meaning of 0 ∈ A(x) + λx − p for a set-valued A (∃ u ∈ A(x) with u + λx − p = 0). ✓
- `def zeroOperator (_ : ℝ) : Set ℝ := {0}`; `def positiveDomain := {z | 0 < z.2}` = ℝ × (0,∞).
- `theorem zero_inclusion_iff (hz : z ∈ positiveDomain) (x) : Solution zeroOperator z x ↔ x = solutionFunction z` with `solutionFunction z = z.1 / z.2` — the full solution set is exactly {p/λ} (both directions, λ > 0). ✓
- `def SingleValuedContinuous A D := ∃ f, ContinuousOn f D ∧ ∀ z ∈ D, ∀ x, Solution A z x ↔ x = f z` — a strong encoding of "single-valued continuous solution map": the entire solution SET equals {f z} with f continuous (not merely a continuous selection). Satisfied via `solution_continuous` (ContinuousOn of p/λ) — real joint continuity. ✓
- `theorem domain_connected : IsConnected positiveDomain` — convexity of univ ×ˢ Ioi 0 with witness (0,1). ✓
- `theorem zero_maximal_monotone` — genuine proof (extension value u at x squeezed by monotonicity against 0 ∈ B(x±1) ⇒ u = 0), so the counterexample survives even adding the customary maximal-monotonicity hypothesis. `zero_not_strongly_monotone` — m·(0−1)² ≤ 0 forces m ≤ 0. ✓
- Decisive: `def ClaimedEquivalence := ∀ A, MaximalMonotone A → ∀ D ⊆ positiveDomain, (SingleValuedContinuous A D ↔ StronglyMonotone A ∧ IsConnected D)` and `theorem conjecture_00000008850_equivalence_false : ¬ ClaimedEquivalence` — instance A = zero operator (maximal monotone), D = positiveDomain (connected), SVC holds, StronglyMonotone fails, so the biconditional's forward direction is false. Since the unrestricted conjectured equivalence implies this restricted one, its negation refutes the original clause. Logic sound; not vacuous (all hypotheses instantiated, LHS genuinely true via exact solution-set identification).
Mathematically: for A ≡ {0} and λ > 0 the inclusion reads λx = p — unique, jointly continuous solution p/λ — while A is not strongly monotone; this correctly breaks the "only if" of the equivalence. The remaining three clauses (closed graph, Hausdorff Lipschitz/cocoercivity, loop-lift deficiency bound) are disclosed as unaddressed; refuting one conjunct refutes the conjunction.
## Issues found
none blocking. (Interpretive note for coordinator: the conjecture does not pin down the parameter domain; the text's own phrasing makes the domain a variable with connectedness as a condition, under which the counterexample D = ℝ×(0,∞) is admissible — λ > 0 is the standard resolvent-inclusion setting. No textual restriction is violated.)
## Verdict rationale
Build, axioms, logs, PDF, and grep all clean; the formalization uses the actual inclusion, actual set-valued operator, actual strong/weak monotonicity and maximality definitions, and proves a genuine non-vacuous counterexample to the literal equivalence clause — one that even strengthens admissibility by restricting to maximal monotone operators. The report is transparent about which clause is refuted and which are not.

## Disposition
APPROVED — merged into main (PR 391). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
