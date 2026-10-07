# Disproof of conjecture 00000007757 (finiteness assertion)

Take the two distinct commuting rational maps `f(z)=z^2` and `g(z)=z^4=f^[2](z)` over `Q`. Their degrees are 2 and 4. Every periodic point of `f` is periodic for `g`, and `f` has infinitely many algebraic periodic points. Hence their periodic-point intersection in `P^1(Qbar)` is infinite, contradicting the conjecture's first assertion and any finite uniform cardinality bound.

The Lean proof uses `K = AlgebraicClosure ℚ` and the standard affine-chart representation `Option K` of the projective line: `some z` represents `[z:1]`, while `none` represents `[1:0]`. `F` and `G` are the projective extensions of the two polynomial maps. The proof verifies their affine formulas, commutation on the full projective line, distinctness, their degrees, and an injective infinite family of common periodic points. The family uses a primitive root of unity of order `2^(n+1)-1` for each `n`.

This refutes the conjecture as written. It does not address an amended statement that excludes maps with a common iterate. The conjecture's separate no-common-iterate clause is not needed to refute the first assertion.

## Reproduce

From `lean/`, run `lake build`. `#print axioms infinite_common_periodic` appears at the end of `Main.lean`.
