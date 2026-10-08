# Author adversarial review: 00000006953

Verdict: PASS on the mathematical counterexample and formal correspondence; fresh build and PDF inspection are recorded separately.

- Equal weights and equal sample costs make allocation proportions unambiguous. The stratum variances are positive, 1 and 4; exactly five samples make the proposed ratio (1,4) integral with both strata represented.
- The sample space is the entire five-fold binary product, not a selected list of favorable samples. Every outcome has mass 1/32 and every full coordinate pattern has mass (1/2)^5. This is the exact independent fair-bit sampling model.
- The sampling measure is an actual `Measure`, proved to have mass one. Expectations are actual Bochner integrals and variances are actual `ProbabilityTheory.variance`; moment values are derived from finite-sum theorems and complete exact evaluation.
- Estimator n uses the first n observations for the first stratum and the remaining 5-n for the second, with both weights 1/2. The proof compares the same usual unbiased stratified estimator under two allocations, avoiding any claim about an unrestricted class of estimators.
- Both estimators have mean zero. The concrete variances 1/2 and 11/24 are proved, and the strict comparison is exact. No random simulation or approximation appears.
- `Optimal` quantifies over all positive allocations of the same fixed total. Showing the admissible allocation n=2 improves upon n=1 suffices to refute optimality. No stronger uniqueness or optimality result is claimed.
- The source says variance, not standard deviation. The submission addresses its literal variance-proportional rule and does not silently replace it with the usual corrected allocation rule.
- The Python supplement independently enumerates all 32 outcomes using Fraction. Lean proves the measure, integral, variance, allocation-ratio, and nonoptimality assertions, and all audited axioms are standard.

This is author self-review. The parent agent separately performs adversarial review before any publication; no external independent review is claimed.
