# Disproof of conjecture 00000007755: infinitely many normalized quadratic PCF parameters

This is a substantive replacement for the argument rejected in PR #826. The old family `(X-a)^2+a` varied only by affine conjugacy and represented a single point of the quadratic parameter space. This revision works in the monic centered family `F_c(X)=X^2+c` and proves that infinitely many **distinct affine-conjugacy classes** in that parameter space are PCF.

Let `K = AlgebraicClosure ℚ`. Define orbit polynomials `P_0(T)=0` and `P_{n+1}(T)=P_n(T)^2+T`. Then `P_n(c)=F_c^[n](0)`. Define `Q_0(T)=1` and `Q_{n+1}(T)=T Q_n(T)^2+1`; induction gives `P_{n+1}(T)=T Q_n(T)`. For every `n≥1`, `Q_n(0)=1` and its coefficient of `T` is 1. Thus `Q_n` is nonconstant and has a nonzero root in `K`.

For each prime `p`, select a root `c` of `Q_{p-1}`. Then `F_c^[p](0)=P_p(c)=0`, while `F_c(0)=c≠0`. The minimal period of the critical point is therefore exactly `p`. Different primes require different parameters. Since the unique critical point of `F_c` is 0, each selected map is PCF. The Lean theorem `infinite_normalized_pcf_parameters` proves that the set of such parameters is infinite.

For completeness, `normalized_affine_conjugate_iff` formalizes that two maps in this monic centered family are affine conjugate only when their parameters agree. This closes the defect identified in the PR #826 review. The theorem `infinite_normalized_quadratic_pcf` also states the resulting infinitude of degree-2 PCF polynomials. All coefficients and all critical points are considered over `K`; no numerical search or unproved classification is used.

This disproves the conjecture's finiteness assertion **even when interpreted up to affine conjugacy**. It does not determine the separate height asymptotic. The conjecture is a conjunction, so a counterexample to its first assertion suffices to disprove it as stated.

## Reproduce

From `lean/`, run `lake build`. The project locks Lean and Mathlib in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. `#print axioms` for the decisive theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
