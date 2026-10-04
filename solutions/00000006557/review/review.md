# Solution Review — Conjecture 00000006557 (PR 359)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "higher-order splitting must contain negative coefficients; ... and the sum of negative coefficients is 1" (高阶分裂必含负系数；负系数的和为 1), within the composition-formula/negative-coefficient criterion statement.
- LaTeX: recompiled in /tmp/tlmc-review2/scratch/pr-359, pdflatex twice exit 0; shipped main.pdf genuine (text ratio 0.9736 vs recompiled — fraction-heavy tables, extraction artifacts only); all 19 files' SHA-256 match VALIDATION.json (independent_check.json identical modulo CRLF; restored pristine after my run).
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings (warningAsError=true; maxHeartbeats/maxRecDepth are effort options only). `#print axioms` on order_four / order_four_after_arbitrary_substitution / conjecture6557_false / magnitude_interpretation_false: only [propext, Quot.sound]. Toolchain lean4:v4.19.0; Std + Std.Internal.Rat only.
- Forbidden content: grep for sorry/admit/native_decide/axiom-decls/unsafe/implemented_by/extern/skipKernelTC over lean/Main.lean and verify.py — no matches. All finite checks are kernel `decide` on exact rationals.
- Auxiliary code: verify.py under python3 — exit 0, output matches shipped independent_check.json (CRLF aside) and verification/auxiliary-verification.log. My own fully independent recomputation, built from the composition T(h) = S(h/6)⁴·S(−h/3)·S(h/6)⁴ with S(t) = exp(tA/2)exp(tB)exp(tA/2) (NOT from the merged list): T = exp(h(A+B)) on all 31 words through degree 4 (formal order ≥ 4); the merged alternating 19-stage list equals the submission's `stages` exactly; negatives {−1/12, −1/3, −1/12} with signed sum −1/2 and absolute sum 1/2; component sums A = 1, B = 1. I also checked the alternative composition-coefficient reading (8×1/6, −1/3): negative sum −1/3 (abs 1/3) — also ≠ 1, so the refutation is robust across all three readings.
## Semantic audit
Literal claim refuted: "the sum of negative coefficients is 1" (负系数的和为 1), stated universally over higher-order splittings. The witness is a genuine higher-order splitting: the Suzuki-type composition with Σc_i = 8·(1/6) − 1/3 = 1 and Σc_i³ = 8/216 − 1/27 = 0, merged into the 19 alternating nonzero stages A:1/12, (B:1/6, A:1/6)×3 pairs, A:−1/12, B:−1/3, A:−1/12, (B:1/6, A:1/6)×3, B:1/6, A:1/12, each component's times summing to 1.

Formalization (lean/Main.lean) uses the same genuine noncommutative-formal-series machinery as the author's PR 358 (words = List Bool, exact exponential series a^n/n!, Cauchy product over all prefix–suffix splits, complete 31-word table for degree ≤ 4, `checked_prefix`/`checked_bounded` lifting kernel decisions to `PrefixEq` for ALL words). The 19-factor product is verified incrementally: each `table_stepN : PrefixEq 4 (multiply (exponential …) table(N−1)) tableN := checked_prefix _ _ (by decide)` is chained by the proved congruence `multiply_prefix` up to `prefix19 : PrefixEq 4 (product stages) table19`, then
```
theorem final_table_exact : PrefixEq 4 table19 exactSeries
theorem order_four : OrderAtLeast 4 stages
```
with table19 = 1/n! on every word of length n ≤ 4 — the exact exp(h(A+B)) series. So formal order ≥ 4 is established by direct computation with no BCH assumption; the tex's BCH-style human proof is consistent with this. Structural facts are all checked on the actual list: `all_stages_nonzero`, `stages_alternate`, `consistent_sums` (A and B sums = 1), `has_negative`. Final theorems:
```
theorem conjecture6557_false : ¬(∀ ss : List Stage, OrderAtLeast 4 ss → negativeSum ss = 1)
theorem magnitude_interpretation_false : ¬(∀ ss : List Stage, OrderAtLeast 4 ss → negativeMagnitudeSum ss = 1)
```
with `signed_negative_sum : negativeSum stages = -1/2` and `negative_magnitude_sum : negativeMagnitudeSum stages = 1/2`, both ≠ 1. The witness is of order ≥ 4, hence inside the "higher-order" class under either the order ≥ 3 or order ≥ 4 reading, and a class member refutes the universal claim. The substitution lemma `order_four_after_arbitrary_substitution` transfers the order condition to arbitrary target algebras (formal ↔ analytic bridge). Non-vacuous: the witness's order and coefficient sums are themselves kernel-verified facts. The submission correctly does NOT refute the necessity clause (its method does contain negative coefficients) — only the numeric "= 1" claim, as disclosed.
## Issues found
none blocking
## Verdict rationale
The Lean project rigorously verifies a bona fide fourth-order splitting (direct degree-4 word-by-word kernel check, no BCH assumption) whose negative coefficients sum to −1/2 signed and 1/2 in absolute value — neither is 1 — and I reproduced every quantity independently from the composition construction, including robustness under the composition-coefficient reading (1/3 ≠ 1). Build is clean with standard axioms only, the PDF is genuine, and all auxiliary outputs and hashes reproduce. The literal "sum of negative coefficients is 1" clause is refuted under every plausible reading.

## Disposition
APPROVED — merged into main (PR 359). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
