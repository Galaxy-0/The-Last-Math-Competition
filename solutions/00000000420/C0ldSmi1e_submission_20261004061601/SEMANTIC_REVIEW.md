# Internal semantic review

This is an internal submission audit, not an official maintainer review.

Both language versions give the same exact formula and interval. The statement claims a probability density with respect to ordinary angular Lebesgue measure in radians, not an expression proportional to an unspecified normalizing constant.

1. **Exact analytic objects.** `rho` is precisely `(2/pi) * cos x * sqrt (1 - sin x)` and `angularInterval` is `Icc (-pi/2) (pi/2)`. Continuity supplies integrability; substitution proves the exact integral `8*sqrt(2)/(3*pi)`.
2. **Nonnegativity before conversion.** `rho_nonneg` proves the displayed density is nonnegative at every point of the interval. The conversion through `ENNReal.ofReal` therefore does not silently alter it on its support. Almost-everywhere nonnegativity is supplied explicitly to the real-integral-to-lintegral theorem.
3. **Actual measure.** `candidateMeasure` is Lebesgue measure restricted to the actual interval, weighted by the actual density using `withDensity`. The total-mass formula and finiteness are proved. The finite-measure wrapper preserves this measure; it does not normalize it.
4. **Actual obstruction.** The mass is strictly greater than one, so the measure fails `IsProbabilityMeasure`. The exact inequality uses proved rational bounds, not floating-point approximations.
5. **Actual weak convergence.** The proof uses Mathlib's `FiniteMeasure` topology, defined by bounded continuous test functions. Total mass is continuous in this topology. Every probability measure has mass one, so no nontrivial-filter limit of probability measures can be the candidate. The final sequence theorem uses the nontrivial `atTop` filter on the natural numbers.
6. **Relation to tableaux.** The final theorem covers every sequence of probability measures. It therefore excludes every potential sequence of angular laws with this advertised weak limit. The disproof does not require a particular tableau model or a formalization of sliding paths; the claimed target itself is impossible.
7. **Scope.** Only the exact advertised density and weak probability limit are ruled out. No actual limit law or renormalized replacement is asserted. Open or closed endpoint conventions do not change the Lebesgue integral.
8. **Trust.** No admissions, extra axioms, unsafe evaluation shortcuts, or altered kernel-check settings occur in the submitted proof sources. The twelve central results have their axiom dependencies printed in the included audit.

An independent agent read all five proof modules and the relevant Mathlib APIs and found no mathematical or semantic blocker. Its source review was separate from the submitting agent's fresh build and direct source replay. The report follows the same proof and states these limits explicitly.
