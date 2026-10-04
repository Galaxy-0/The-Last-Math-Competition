# Solution Review — Conjecture 00000007790 (PR 427)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004075335`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff adds only the correctly named personal submission folder. Base metadata marks conjecture 00000007790 unsolved, and no prior solution history exists. The submitted bilingual `conjecture.md` is byte-identical to the official file.
- **LaTeX and PDF.** I read the complete three-page report and every submitted source/configuration file. A fresh `latexmk -pdf` build succeeded (exit 0; 3 pages). I extracted both shipped and fresh PDF text, normalized them for compiler/ligature differences, and rendered all fresh pages with Ghostscript. Content and section order match. No auxiliary numerical program is used or required.
- **Lean.** After preseeding the official Mathlib cache, `lake build` completed successfully, building all five library modules and the root theorem. Every submitted Lean file was independently replayed with warnings treated as errors: `Definitions.lean`, `Law.lean`, `LogConcavity.lean`, `Moments.lean`, `Tail.lean`, `Conjecture7790.lean`, and `Check.lean`; all exited 0. Twenty-four central axiom audits report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No proof escape, custom axiom, unsafe declaration, implementation override, native decision shortcut, or kernel-trust override occurs. The only “axiom” lines are legitimate `#print axioms` audits.
- **Independent mathematics.** I independently checked normalization and moments `1,1,2`, the density/log-concavity inequality, the exact tail `e^{-(u+1)}`, and the logarithmic form of the eventual Gaussian-bound contradiction.

## Semantic audit

The official first assertion claims a sub-Gaussian norm bound for isotropic log-concave vectors. It does not exclude dimension one or require bounded/symmetric support. In dimension one, `√n=1`, the Euclidean norm is absolute value, and isotropy means mean zero and second moment one.

Let `Y` have the rate-one exponential density `e^{-y}1_{y≥0}`, and set `X=Y-1`. Then `X` has density

`f(x)=e^{-(x+1)}1_{x≥-1}`.

Its integral is one, `E[Y]=1`, and `E[Y²]=2`, hence `E[X]=0` and `E[X²]=1`. Lean establishes these facts for the actual pushed-forward measure, including integrability, rather than assuming a formal probability distribution with stipulated moments.

The density is genuinely log-concave. On its convex positive support `[-1,∞)`, `log f(x)=-(x+1)` is affine. If a convex-combination input has positive density but an endpoint has density zero, the weighted geometric mean is zero for positive weights. Endpoint weights are handled separately. Lean proves the full weighted inequality including zero-density points, not merely concavity on the positive support. Thus the one-dimensional law is admissible under the standard definition of an isotropic log-concave measure.

For `u≥-1`, `P(X>u)=P(Y>u+1)=e^{-(u+1)}`. For `u≥0`, `{X>u}⊆{|X|≥u}`, so `P(|X|≥u)≥e^{-(u+1)}`. Given any proposed positive threshold and decay constants `A,c`, and any eventual starting time `T`, choose

`t=max(max(T,1),(A+2)/c+1)`.

Then `ct>A+2`, so `ct²>(A+2)t>At+1`. Therefore

`e^{-ct²}<e^{-(At+1)}≤P(|X|≥At)`.

This violates the sub-Gaussian bound even if it is imposed only for sufficiently large `t`. Lean formalizes this for every `A,c,T>0` with the stated positivity conditions, and then negates a one-dimensional Gaussian claim with independent positive constants and an eventual threshold. That formal claim is deliberately weaker than the original universal assertion, so its negation refutes the original. The counterexample law is fixed and fully admissible, so the result is non-vacuous.

The later extremality and non-improvability clauses are not needed: the first universal κ=2 assertion is already false. The report clearly distinguishes the proved necessary consequence from claims about extremizers.

## Verdict rationale

This is the standard one-dimensional obstruction to a norm sub-Gaussian estimate for all isotropic log-concave laws: an exponential tail is heavier than any Gaussian tail. The formalization constructs the actual Mathlib measure and density, proves admissibility, derives an exact lower tail bound, and defeats every positive Gaussian constant eventually. Builds, strict replays, axiom audits, scans, PDF verification, and independent computations all pass.

## Disposition

APPROVED — ready for merge (PR 427). No merge action was taken by this reviewer.
