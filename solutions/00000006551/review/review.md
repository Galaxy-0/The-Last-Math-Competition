# Solution Review — Conjecture 00000006551 (PR 358)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "the error coefficient of the leading commutator [of a first-order splitting] is always one half, and the coefficient saturates in the noncommuting case" (首换位子的误差系数恒为二分之一；无交换情形的系数饱和), with the source's own Definition: first-order splitting = any first-order approximation scheme of fractional stepping.
- LaTeX: recompiled in /tmp/tlmc-review2/scratch/pr-358, pdflatex twice exit 0; shipped main.pdf genuine (text ratio 0.9815 vs recompiled — math-dense doc, diffs are formula-layout extraction artifacts); all 19 files' SHA-256 match VALIDATION.json (independent_check.json regenerated identically modulo CRLF; restored pristine).
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings (warningAsError=true); `#print axioms` on order_one/degree_two_error/actual_matrix_error/conjecture6551_false: only [propext, Quot.sound]. Toolchain lean4:v4.19.0; `import Std` + `Std.Internal.Rat` (bundled only), exact rational arithmetic.
- Forbidden content: grep for sorry/admit/native_decide/axiom-decls/unsafe/implemented_by/extern/skipKernelTC over lean/Main.lean and verify.py — no matches. Finite checks use kernel `decide` on exact rationals (legitimate).
- Auxiliary code: verify.py under python3 — exit 0, output matches shipped independent_check.json byte-for-byte (CRLF aside) and matches verification/auxiliary-verification.log. My own independent exact formal-series computation (built from scratch, including a Lie–Trotter cross-check): split coefficients at degree 2 are A²:1/2, AB:3/4, BA:1/4, B²:1/2 vs exact 1/2 each, so error = (1/4)[A,B] with zero error at degrees 0 and 1; AB coefficient 3/4 ≠ 1/2 confirms exactly order 1; Lie–Trotter gives exactly (1/2)[A,B] as expected. [A,B] = diag(1,−1) ≠ 0 for the given nilpotent pair.
## Semantic audit
Literal claim refuted: "The error coefficient of the leading commutator is always one half" (恒为二分之一). The source's Definition sentence itself defines the class ("first-order approximation scheme of fractional stepping"), not a single formula; the "always" makes it universal over that class.

Formalization (lean/Main.lean): words are `List Bool` (A/B letters), series are coefficient functions `Word → Q`; `exponential letter a w` gives a^n/n! on the pure letter-word and 0 elsewhere (the exact exp(ahA) as a noncommutative formal series); `multiply` is the genuine Cauchy product over all prefix/suffix splits of each word (with `split_reconstruct`/`split_complete` sanity lemmas); `product stages` for `stages := [(false,3/4),(true,1),(false,1/4)]` is exactly Φ_h = exp(3hA/4)·exp(hB)·exp(hA/4); `exactSeries w = 1/|w|!` is exp(h(A+B)). The finite check list `wordsFour` (31 words) is structurally proven complete for degree ≤ 4, and `checked_bounded` connects kernel-decided table checks to `PrefixEq` (agreement on ALL words of degree ≤ n) — so the degree-≤2 verification covers all four words AB, BA, A², B², not a sample.

Key theorems:
```
theorem exactly_first_order : ExactlyFirstOrder stages   -- OrderAtLeast 1 ∧ ¬OrderAtLeast 2
theorem degree_two_error : PrefixEq 2 (errorSeries stages) (fun w => (1/4 : Q) * commutator w)
theorem leading_not_half : ¬ LeadingCoefficient stages (1/2)
theorem leading_not_negative_half : ¬ LeadingCoefficient stages (-1/2)
theorem conjecture6551_false :
    ¬(∀ ss : List Stage, ExactlyFirstOrder ss → LeadingCoefficient ss (1/2))
```
`LeadingCoefficient ss c := ∀ w, w.length = 2 → errorSeries ss w = c * commutator w` with `commutator` = +1 on AB, −1 on BA; `leading_coefficient_unique` pins the coefficient uniquely at 1/4, so no reading (sign convention, which word, whole-error-vs-commutator-part) escapes: the degree-2 error is exactly (1/4)[A,B] with vanishing A²/B² parts. The method is exactly order one (not a higher-order method, whose coefficient 0 would be an unfair witness), stage times sum to 1 per component (3/4+1/4 = 1; 1), positive coefficients — a legitimate fractional-step splitting. The saturation clause is refuted on a genuinely noncommuting instantiation: `matrices_noncommuting`, `actual_matrix_error` (degree-2 error entrywise equals (1/4)(AB−BA)), `actual_matrix_error_nonzero` (diag(1/4,−1/4) ≠ 0). The substitution lemmas (`evaluation_congr`, `all_degree_evaluations`, `order_one_after_arbitrary_substitution`) transfer formal-series equalities to arbitrary target algebras, closing the formal-vs-analytic gap; with nilpotent 2×2 matrices the exponentials are finite polynomials, so the formal computation IS the analytic Taylor comparison.

Interpretation disclosure (the one judgment call): under the narrowest possible reading — "first-order splitting" = only the two-factor Lie–Trotter formula exp(hA)exp(hB) — the coefficient is indeed always 1/2 and the conjecture would hold. But the conjecture's own Definition sentence ("first-order splitting is the first-order approximation scheme of fractional stepping" / 一阶分裂为分步求解的一阶逼近格式) defines the class of first-order fractional-step schemes, and "always" quantifies over it; per the competition's authoritative-literal-statement adjudication this class reading governs. The tex explicitly discloses this and makes no claim about Lie–Trotter itself.
## Issues found
none blocking
## Verdict rationale
The Lean project models actual noncommutative exponential products as formal series with complete (not sampled) degree-≤2 verification, proves the witness is exactly first order, and pins its leading commutator coefficient uniquely at 1/4 ≠ ±1/2 — refuting the "always one half" claim under the conjecture's own class definition, with the noncommuting-saturation clause refuted by concrete matrices. My independent computation reproduces every number, the build is clean with standard axioms only, and all auxiliary outputs and hashes check out. The narrow Lie–Trotter-only reading is the sole escape and is disclosed and excluded by the source's own Definition sentence.

## Disposition
APPROVED — merged into main (PR 358). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
