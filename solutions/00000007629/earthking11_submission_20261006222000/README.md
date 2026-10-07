# Disproof of conjecture `00000007629`

The source states that rotor realizations of basis changes are unique, with
orientation reversal as the stated exception. Read literally, this is false
even for the orientation-preserving identity change of an orthonormal basis.

The Lean development uses Mathlib's actual Clifford algebra and actual
`CliffordAlgebra.spinGroup`. The vector space is `Fin 2 → ℝ` and the quadratic
form is

`Q(v) = v 0 * v 0 + v 1 * v 1`.

The named standard basis is `Pi.basisFun ℝ (Fin 2)`. The proof verifies that
each basis vector has quadratic norm 1 and that the polar form of distinct
basis vectors is zero. The identity linear map preserves `Q`, fixes every
basis vector, and has determinant 1.

For the actual spin-group action used here, a rotor `r` realizes a linear map
`T` when `r * ι(v) * star(r) = ι(T v)` for every vector `v`. Both scalar
Clifford elements `1` and `-1` belong to Mathlib's spin group: the proof of
`-1` membership factors it as the product of the units `ι(e₀)` and `ι(-e₀)`
in the generating set of the Lipschitz group, then proves pin-group unitarity
and evenness. They are distinct, yet both induce the identity action on every
vector. Consequently the identity basis change, which has determinant 1, has
at least two rotor realizations, and the formal statement `∃! rotor, ...` is
false.

This disproof addresses uniqueness literally. If an intended convention
identifies rotors modulo the central sign `{1, -1}`, that quotient must be
stated in the conjecture; the source does not include such an identification.
The Lean project compiles without `sorry`, `native_decide`, or extra axioms.
