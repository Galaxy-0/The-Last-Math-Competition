# Disproof of 00000008342

For the full set of integer triples on x²+y²+z²=n², every coordinate has absolute value at most n and (n,0,0) attains n. Hence the actual supremum of coordinate heights is n. Its ratio to sqrt(n²/3) is sqrt(3), not one; an additional factor 1/3 in the Chinese wording also fails.

The report addresses the explicit maximal-coordinate reading, not a statistical mean or typical-height statement. It refutes only that conjunct.

`lean/Main.lean` verifies the actual integer sphere, all-point bound, attained supremum, unbounded square sequence, exact ratios and limits. Final theorems: `Counterexample.no_claimed_asymptotic` and `Counterexample.no_third_asymptotic`.

Reproduce with Lean 4.19.0:

```sh
cd lean
lake exe cache get
lake build
```

Mathlib pin: `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Public dependency pins are committed. Compile the PDF using `tectonic report.tex`.
