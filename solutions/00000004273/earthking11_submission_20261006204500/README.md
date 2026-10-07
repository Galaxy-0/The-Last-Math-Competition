# Conjecture 00000004273: finite counterexample

The Lean development uses the actual additive group `G = ZMod 2 × ZMod 4`.
For each natural number `n`, `powerImage n` is the image of multiplication by
`2^n`, `twoTorsion` is the kernel of multiplication by `2`, and
`UlmLayer n = (2^n G)[2]`. `UlmQuotient n` is the standard additive-group
quotient `U_n / U_{n+1}`. Thus `CardinalSequence n` is literally the cardinal
of the requested Ulm quotient, not a separately postulated certificate.

The code proves that the quotients at indices 0 and 1 are each isomorphic to
`ZMod 2`, so their cardinalities are equal. A single equality at consecutive
indices refutes strict anti-monotonicity; later ordinal stages are unnecessary
for this counterexample to a claim requiring strict decrease at every stage.
The example is finite (hence countable) and 2-primary, with exponent dividing
4, as Lean theorems in `Main.lean` verify.

Build with Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` using `lake build`.

The iteration defining `powerImage` is formally identified with
multiplication by `2^n` via `iterDouble_eq_power_smul`. This identifies
the concrete subgroup construction with the standard finite Ulm layers.

## Previous closed attempt

PR #309 already proposed this finite counterexample. It was closed without
a rejecting review. Its capstone used a tailored proposition excluding two
simultaneous quotient certificates, rather than directly defining the
actual cardinal-valued sequence and negating its strict anti-monotonicity.
This replacement credits that example and supplies the direct sequence
bridge with Mathlib's group and quotient objects. It also prints foundational
axiom dependencies for the actual capstone, not only numeric calculations.

The report is `solution.tex` and its compiled PDF `solution.pdf`. Run
`lake update`, `lake exe cache get`, and `lake build` inside `lean/`.
The pinned lockfile is included. There are no unfinished proofs, native
evaluations, or custom axioms. The finite checks only cover the eight group
elements and the quotient coordinate maps.
