# Independent semantic review: conjecture 00000007790

Review completed: 2026-10-04T07:59:08.360596+00:00

Outcome: PASS. No blocking semantic or report-to-source discrepancy found.

## Scope and method

Read every line of the six library Lean source files and Check.lean, the final report main.tex and README.md, and the exact English and Chinese conjecture at upstream revision 0862407ef50dda4f7376342ca3e79368dce942d2. Inspected the pinned Mathlib exponential-density, probability-normalization, CDF, real-measure-complement, Gamma-integrability, and Gamma-integral definitions/theorems used by the argument. This is an independent mathematical and source-level review; it does not replace the submitting agent's separate clean-build, strict-replay, axiom-output, or PDF verification records. No source changes or compilation were performed in this review.

Source: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/0862407ef50dda4f7376342ca3e79368dce942d2/conjectures/00000007790.md

Primary definition reference: Olivier Guédon and Emanuel Milman, Interpolating Thin-Shell and Sharp Large-Deviation Estimates for Isotropic Log-Concave Measures, arXiv:1011.0943v3 (2 June 2011), introduction pp. 1–2, https://arxiv.org/pdf/1011.0943v3. Isotropy is centering with identity covariance; the negative log of a log-concave density is an extended-real convex function. Zero density outside a convex support is allowed. The counterexample does not rely on the paper's concentration theorems.

## Mathematical correspondence

1. Exact domain and dimension. Both source languages assert the Gaussian norm-tail bound for isotropic log-concave random vectors and do not exclude dimension one or require symmetry, bounded support, or strong log-concavity. At n=1 the Euclidean norm is absolute value and sqrt(n)=1. Disproving a necessary one-dimensional consequence is sufficient to refute the first conjunct of the stated conjecture. No claim to settle the subsequent sharpness or extremizer assertions separately is needed.

2. Actual measure and density. Definitions.lean:11–16 defines the law as the genuine push-forward of Mathlib expMeasure 1 under y -> y-1 and the explicit nonnegative density exp(-(x+1)) on [-1,infinity), zero elsewhere. Law.lean:9–35 proves, rather than assumes, the pointwise relation to the exponential PDF and equality of that push-forward with Lebesgue measure weighted by the proposed density. Its translation-of-integrals argument uses measurable sets and a measurable translation; the direction of the shift and the support endpoint are correct.

3. Normalization and real probabilities. Moments.lean:55–58 proves IsProbabilityMeasure for the actual pushed-forward measure using Mathlib's positive-rate exponential normalization and measurable-map theorem. Therefore the real-valued measures used in the tail are finite actual probabilities; ENNReal.toReal cannot turn an infinite mass into a spurious zero. Tail.lean also supplies the required probability instances locally before using complement and monotonicity.

4. Integrable isotropic moments. Moments.lean:17–52 links integrability and integration against expMeasure 1 to Lebesgue integrals and proves every natural moment integrable with value n!. The first and second centered moments are separately proved integrable at lines 60–84, and their values 0 and 1 are calculated at lines 86–138. Thus IsIsotropic includes actual integrability, and none of the moment equalities exploits a default value for a nonintegrable Bochner integral. Zero mean plus unit second moment is exactly covariance 1 in dimension one.

5. Full log-concavity. Definitions.lean:19–22 uses the nonnegative weighted-power definition for all points and all nonnegative weights summing to one. LogConcavity.lean:26–52 handles zero weights first, positive-support points by an exact affine exponent identity, and zero-density points using the vanishing positive power. This covers the support boundary and all zero-density cases, not merely concavity of log on an unspecified set. Lines 16–24 and 55–70 additionally identify the positive support as the convex half-line and prove that log density is affine there. The resulting extended negative log is x+1 on that half-line and +infinity elsewhere, satisfying the primary reference's definition.

6. Actual tail from CDF. Tail.lean:9–30 derives expMeasure 1 (Ioi u) from the proved CDF on Iic u and finite-measure complementation, then computes the shifted interval preimage. The exact result is the open right tail P(X>u)=exp(-(u+1)) for u>=-1. Lines 33–40 use event inclusion to obtain P(|X|>=u)>=exp(-(u+1)) for u>=0. The final argument requires only this lower bound, so no atomlessness or exact absolute-tail equality is needed.

7. Quantifiers and contradiction. Tail.lean:43–57 fixes the same law and proves failure for every A>0, c>0, and real starting threshold T. The explicit t=max(max(T,1),(A+2)/c+1) gives t>=1, t>=T, and c*t^2>A*t+1. Strict exponential monotonicity yields the contradiction to the Gaussian upper bound. The top-level theorem at Conjecture7790.lean:36–47 combines the qualifying law and this universal failure. Allowing independent threshold and decay constants and an arbitrary starting threshold weakens the conjectured bound, so its failure also rules out a shared positive constant. Even constants or a starting threshold chosen for this particular distribution cannot work.

## Report agreement

Final report and README rechecked: 2026-10-04T08:02:07.679068+00:00. The report layout changes and shortened opening formal-correspondence paragraph preserve the mathematical meaning. The README accurately describes the actual measure, full qualifying properties, tail lower bound, all-constants contradiction, and one-dimensional scope. Its seven-file replay sequence covers the six library sources and Check.lean in dependency order; the 24 audit count and pinned Mathlib revision agree with the frozen sources and manifest. All seven previously reviewed Lean files retain exactly their recorded hashes.

The reviewed main.tex correctly describes the actual distribution and density, normalization, integrable moments, full log-concavity, open right-tail identity, absolute-tail lower bound, and explicit all-constants witness. The ordinary integral calculation in the mathematical explanation and the stated Gamma-integral implementation are consistent. It identifies the final Lean theorem as negation of the necessary one-dimensional consequence, and confines the disproof to the first conjecture assertion. The reference is used only to fix standard definitions; no claim is made against the established Paouris exponential estimate.

The report accurately describes Lean 4.19.0, the Mathlib v4.19.0 requirement, and exact revisions in the manifest. There are six library source modules, seven submitted Lean files when Check.lean is included, nine pinned dependencies, and 24 public theorem/instance #check and #print axioms audit directives. No sorry, admit, custom axiom, unsafe, or native_decide token occurs in the reviewed Lean sources. This source scan does not substitute for checking the generated axiom output. Final package presence, exact bilingual copy, staged-file hashes, and build/replay logs remain packaging checks for the submitting agent.

## Reviewed content hashes (SHA-256)

```text
83671b491b6e524a7d769cddc253b193931d73ddc4684d27fd3a9b9d1b780df8  Conjecture7790.lean
66459ef66a719b3b962e61de17f8f13b0b56d2ddb74540f62ced75a68fbd4c4e  Conjecture7790/Definitions.lean
795a8b9a9da633e011733bb14b49933293ec96e6041c3300dbee9c1fb204df1c  Conjecture7790/Law.lean
bd35f1d5c087e13fd429922c59212bb4aa760b676d9405f0323e9ddba5e3b245  Conjecture7790/LogConcavity.lean
ff673c418ed4abe220470434c629aa96263e164bf5d5f01139c11fe9b1762552  Conjecture7790/Moments.lean
b42bced8e2b9c05402b2a1abe14d6c5405aad2240215d5557afd2fcb9762df84  Conjecture7790/Tail.lean
7e4e0ba26ddfc8f225672a74f4b85151e505f9b57ea1d3d8cd45cc395b034190  Check.lean
89d332d7f12a7e1ede5873c1bdf0416d35e8b09696aa8906f2c2851176365fc1  main.tex
0da3a0d5fec6550bc54c018169654bb29586f8fbfb8de117e0669a25876f6ad8  README.md
```
