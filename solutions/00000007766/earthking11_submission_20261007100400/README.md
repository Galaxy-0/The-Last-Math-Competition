# Disproof of conjecture 00000007766 (value-set assertion)

The conjecture says that the difference of two canonical heights, evaluated on periodic points in `P^1(Qbar)`, has a value set containing **every real number** at least some positive constant `c` (and also 0). This is impossible by cardinality alone. The algebraic closure `Qbar` is countable, so `P^1(Qbar)` and every subset of it are countable. The image of any such subset under any real-valued function is countable. The real ray `[c,∞)` is uncountable.

The Lean file uses `K = AlgebraicClosure ℚ` and the affine-chart representation `Option K` of `P^1(K)`. It proves this type countable and the upper ray uncountable. It then defines periodicity under an arbitrary self-map `F` and proves that the image of its periodic points under **any** function `D : P1 → ℝ` cannot contain that ray. This applies in particular to the conjectured canonical-height difference, independent of its formula or the dual-map convention.

This refutes the literal value-set claim. It does not analyze the separate tail-asymptotic claim.

## Reproduce

From `lean/`, run `lake build`. `#print axioms no_claimed_value_set` appears at the end of `Main.lean`.
