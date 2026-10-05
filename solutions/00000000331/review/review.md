# Solution Review — Conjecture 00000000331 (PR 600)

**Submitter:** C0ldSmi1e  
**Submission:** `solutions/00000000331/C0ldSmi1e_submission_20261005041510/`  
**Head:** `56946315f66054a68885746ca29678f413eca701`  
**Result:** Approved

## Claim

The official statement literally says that if \(\sum \psi(n)/n=\infty\), then for Lebesgue-almost every \(\alpha\), infinitely many positive integers \(n\) satisfy \(|\alpha-a/n|<\psi(n)\), where \(a\) is fixed. The submission disproves this displayed fixed-numerator implication for every real \(a\), without claiming to resolve a differently formulated inhomogeneous Duffin–Schaeffer problem.

## Mathematical audit

Set \(\psi(n)=1/4\). The series is one quarter of the harmonic series and diverges to \(+\infty\), so the hypothesis holds. This function is positive, bounded, and nonincreasing; the official statement imposes no decay condition.

Fix any real \(a\). For sufficiently large \(n\), \(|a|/n<1/4\). Therefore every \(\alpha\in[1/2,3/4]\) satisfies

\[
\left|\alpha-\frac an\right|
\ge \alpha-\frac{|a|}n
>\frac12-\frac14
=\frac14=\psi(n).
\]

Thus each such \(\alpha\) has only finitely many successful denominators. The interval \([1/2,3/4]\) has Lebesgue measure \(1/4>0\), so the claimed almost-everywhere conclusion fails on the real line and on every standard unit-interval domain. The counterexample is explicit and non-vacuous and works for every fixed real numerator.

## Formal statement correspondence

Lean defines the partial sums over exactly \(1,\dots,N\), divergence as `Tendsto ... atTop atTop`, and success as membership in the actual set of positive \(n\) satisfying `|α - a/n| < ψ n`. `InfinitelyApproximable` requires that set to be infinite. The numerator \(a\) remains fixed.

`LiteralClaim` quantifies over strictly positive radii and a specified measure; `NonnegativeLiteralClaim` covers the broader nonnegative reading. `radius_diverges`, `hits_finite`, `failureInterval_volume_pos`, and the AE lemmas establish the counterexample. `literal_claim_false` and `nonnegative_literal_claim_false` refute both readings for Lebesgue measure on \(\mathbb R\) and on \([0,1]\). Open and half-open interval conventions are also proved to fail.

## Verification

The complete LaTeX and Lean sources were independently reviewed. A fresh pdfLaTeX rebuild produced the expected two pages. The linked Lean 4.19 project built successfully. Direct warning-as-error replays passed for the proof source, `Check.lean`, and the environment inventory.

`Check.lean` printed all eight definitions and all 20 authored theorem types and axiom dependencies. The complete environment inventory found exactly 37 constants from the proof module, including nine generated constants, with no unsafe, partial, or axiom declarations. Every theorem used only `propext`, `Classical.choice`, and `Quot.sound`.

Both Python auxiliary scripts were syntax-checked and independently replayed. The verifier passed dependency-pin, fresh-build, strict-replay, source-declaration, forbidden-token, and environment checks. PDF export replay succeeded. All 35 packaged SHA-256 entries matched. All required harmonic-divergence, finiteness, measure, and AE coverage is symbolic in Lean; no external numerical computation is needed.

Scans found no `sorry`, admission, custom axiom, `native_decide`, unsafe implementation, `implemented_by`, `extern`, kernel-check bypass, or incomplete proof. Base metadata marks the conjecture unsolved and no duplicate solution directory existed.

## Conclusion

This is a complete, faithful, independently replayed disproof of the literal official claim. Approved.
