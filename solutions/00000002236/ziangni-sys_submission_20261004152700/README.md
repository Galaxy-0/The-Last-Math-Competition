# Disproof of conjecture 00000002236

The fixed coprime quadratics f=X² and g=X²−1 have composition-iterate polynomial gcd degree exactly 2^k at indices (k,2k). Their actual integer evaluations at the fixed starting point 2 have gcd exactly 2^(2^k) at the same indices. Both families are unbounded despite fixed original degrees 2. Thus both polynomial and evaluated-integer readings of the source fail.

Lean defines actual polynomials, recursive composition iterates, a Bezout identity proving coprimality, the degree assertions, the even-iterate recurrence, and a common-factor divisibility theorem over arbitrary commutative rings. It uses Mathlib's actual polynomial gcd/natDegree and actual integer-polynomial evaluation/Int.gcd. The unboundedness theorems quantify over every natural bound.

Reproduce from lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Ignored local junctions only reuse the cache. The full build prints six axiom audits. No admitted proofs, custom axioms or native decision procedures.

The one-page disproof.tex/disproof.pdf includes both complete arguments. Built-in editor/compiler was attempted with the known platform-directory failure, followed by successful Tectonic compilation and Poppler visual QA. A stray plus sign found during initial PDF QA was removed and the final PDF was recompiled and inspected.