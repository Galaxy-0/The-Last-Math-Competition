# Solution Review — Conjecture 00000008492 (PR 405)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004045124`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — universal spectrum of mean-convergence rates of random subadditive sequences claimed dominated by log n/n (logarithmic harmonic spectrum law); slowest systems from Sturmian/Thue–Morse; matching bounds
- LaTeX: report.tex recompiled in /tmp/tlmc-review5/scratch/pr-405 with pdflatex (2 passes), exit 0, 0 errors, 2 pages; shipped report.pdf is a real PDF 1.5; VERIFICATION.md consistent with my reproduction
- Lean build: exit 0 ("Build completed successfully", 2166 jobs); only output is 6 `#print axioms` info lines, each exactly [propext, Classical.choice, Quot.sound]
- Forbidden content: grep over own Main.lean for sorry/admit/native_decide/`axiom `/unsafe/implemented_by/extern/skipKernelTC: no hits; no #eval or computational shortcuts
- Auxiliary code: no scripts (VERIFICATION.md: "No auxiliary computation is required" — confirmed, everything is proved); independent python3: sqrt(m+n) ≤ sqrt m + sqrt n verified; mean = 1/√n vs log n/n — ratio √n/log n = 4.6, 72, 1526, 36191 at n=10³…10¹², diverging, so mean is not O(log n/n) — matches the Lean theorems
## Semantic audit
Conjecture literal clause 1 (EN/CN): "The universal spectrum of convergence rates is dominated by log n/n" / 收敛速率的普适谱由 log n/n 主导. Under either reading — (a) every system's error is O(log n/n), or (b) the slowest rate in the spectrum is log n/n (as reinforced by clause 2's "slowest converging systems") — the claim is a universal upper rate bound over subadditive processes. The submission exhibits a process in the class whose error exceeds every eventual constant multiple of log n/n.

Lean encoding (all genuine Mathlib objects):
- `abbrev Ω := Unit`, `def μ : Measure Ω := Measure.dirac ()`, `instance : IsProbabilityMeasure μ`, `def T : Ω → Ω := id`; `theorem system_ergodic : Ergodic T μ` — a genuine ergodic probability-preserving system (one-point space; only trivial invariant sets).
- `def X (n : ℕ) (_ : Ω) : ℝ := Real.sqrt n` with `integrable_X`, `X_nonneg`, `X_zero`; `theorem subadditive_process (m n : ℕ) (ω : Ω) : X (m + n) ω ≤ X m ω + X n ((T^[m]) ω)` — the actual subadditive cocycle inequality with the iterate T^[m] (proved via `Real.sqrt_le_iff`).
- `theorem expectation_X : (∫ ω, X n ω ∂μ) = Real.sqrt n` — actual Bochner integral against the Dirac measure; `mean n = (∫ ω, X n ω ∂μ) / n`; `mean_tendsto_zero : Tendsto mean atTop (𝓝 0)` and pointwise version — the convergence whose rate is at issue; the one-sided error equals mean n ≥ 0.
- `theorem log_div_sqrt_tendsto_zero : Tendsto (fun n : ℕ => Real.log n / Real.sqrt n) atTop (𝓝 0)` from `isLittleO_log_rpow_atTop`.
- Key theorem `no_eventual_rate (C : ℝ) (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ C * (Real.log n / n) < mean n` — defeats EVERY constant and EVERY starting index, so the failure is not a coefficient artifact.
- Final theorem `not_bigO : ¬ Asymptotics.IsBigO atTop mean (fun n : ℕ => Real.log n / n)` — negation of Mathlib's actual norm-based IsBigO, i.e., the mean-convergence error is not O(log n/n). This directly contradicts the conjecture's dominance clause.

Hypotheses are those of the conjecture's own setting: an ergodic measure-preserving probability system, a nonnegative integrable subadditive process (each X_n integrable; the conjecture imposes no uniform bound on sup_n‖X_n‖∞, no mixing, no aperiodicity). Not vacuous: the process really converges (mean_tendsto_zero) yet slower than the claimed universal rate; the contradiction uses the actual IsBigO definition. Since the universal-rate clause fails, the conjunction fails; clauses 2–3 about Sturmian/Thue–Morse constructions cannot restore it.
## Issues found
none blocking. FLAG for coordinator attention (per your rule on degenerate counterexamples): the underlying ergodic system is the one-point space with the identity map — a trivial/deterministic member of the class. The conjecture text carries no restriction (no mixing, no nontriviality, no uniform bound) and a deterministic process is a legitimate "random subadditive sequence"; the disproof even allows process-dependent constants. I judge it acceptable under the repo's literal-statement precedent, but it is the one judgment call in this batch.
## Verdict rationale
The Lean project constructs, from Mathlib's actual ergodicity, Bochner-integration and asymptotic definitions, an integrable nonnegative subadditive process on an ergodic probability system whose mean error 1/√n provably (no_eventual_rate, not_bigO, standard axioms only) fails O(log n/n) — refuting the conjecture's universal logarithmic-harmonic rate clause under any coherent reading. The counterexample sits inside the conjecture's stated class with no extra hypotheses smuggled in; the only caveat is the triviality of the chosen ergodic system, disclosed in the report, which the unrestricted conjecture text permits.

## Disposition
APPROVED — merged into main (PR 405). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
