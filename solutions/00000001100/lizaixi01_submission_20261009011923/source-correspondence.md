# Source correspondence for 00000001100

Exact source copy: `00000001100.md`.
SHA256: `24687c041da4b65025f681b6d475e874c8ecc52a6487a7e17bb9effa4daf648d`.
Final worker Lean input: `Main.lean`.
SHA256: `34b6c60b727d2f0e8bf3156349eb66db7adef56caf428355cde480908c4f097c`.

## Necessary clause being refuted

English says the natural-action orbit count of a maximal subgroup is always
`q` plus a uniformly bounded constant term. Chinese makes the same assertion:
“极大子群的轨道计数恒为 q 加一致有界常数项”. The proof takes `q` to be the
cardinality of the finite field. This is the conventional finite-field parameter,
and `FiniteFieldOrbitCountClause` explicitly uses `Nat.card F`.

The source does not give a precise definition for its additional kernel/subfield
phrase. We do not invent one. A conjunction with a false necessary first clause
is false whatever its additional clause means. The theorem
`refutation_with_additional_clause (additionalClause : Prop)` records exactly
that elementary logical consequence. `additionalClause` is not a mathematical
model of the undefined phrase and is not an assumption of the refutation.

## Objects and quantifiers

| Source object or quantifier | Lean object or theorem |
| --- | --- |
| Finite field, with size `q` | `F : Type`, `[Field F]`, `[Finite F]`, `q = Nat.card F` |
| Affine group of the field line | `AffineGroup F := F ≃ᵃ[F] F`, mathlib's actual affine equivalence group |
| Natural action | `naturalAction`, evaluation `f • x = f x`; multiplication is composition |
| Maximal proper subgroup, in the inclusion order | `H : Subgroup (AffineGroup F)` with `IsCoatom H` |
| Actual number of natural-action orbits of `H` | `orbitCount F H := Nat.card (MulAction.orbitRel.Quotient H F)` |
| Uniformly bounded signed constant term | `∃ C : Nat`, followed by `∃ c : Int`, `count = q + c`, `c.natAbs ≤ C` |
| “Always” | The proof allows any exceptional threshold `q0`; negating this eventual version also negates “always” |
| All finite fields and all maximal subgroups | `FiniteFieldOrbitCountClause` quantifies these directly |
| Counterexample family | Every `C,q0` admits a prime field `ZMod p`, `p≥q0`, with a certified maximal `H` and `count(H)+C<p` |

The one-dimensional group is a standard finite-field affine group and therefore
is an admissible family for the source's universal claim. Nothing in either
language excludes point stabilizers, prime fields, the field line, or small
fields. The generic stabilizer and orbit proofs work over every field, including
the prime field of order two. No unsupported small-field exception is used.

## Uniformity and real constants

The actual difference of the two cardinalities is an integer. If the source
intended a real uniform absolute bound `B`, take any natural integer
`C ≥ max(B,0)` (for example, an appropriate ceiling). The equality
`count = q + c` with `|c|≤B` implies `q ≤ count+C`. Thus it implies the weaker
`EventuallyUniformLowerBound`. The theorem
`not_eventuallyUniformLowerBound` refutes that necessary consequence for every
natural `C` and every threshold `q0`. It consequently covers real error bounds,
negative/zero/positive signed constants, and an eventual asymptotic reading.
The source's constant is not assumed nonnegative; its uniform absolute bound
can be chosen nonnegative without loss.

## The actual bridge to two orbits

No theorem assumes that orbit count is two. `move_nonzero` constructs a genuine
affine scaling by the unit `y/x`. `zeroStabilizer_isCoatom` proves maximality
using arbitrary overgroups and actual group multiplication. The theorem
`zeroStabilizer_orbitRel_iff` then proves that two points are in the same orbit
exactly when both are zero or both are nonzero.

`zeroStabilizer_orbitQuotientEquivBool` builds a genuine quotient equivalence:
the zero class maps to `true`, the nonzero class to `false`; its inverse selects
0 and 1. Its two inverse laws are proved. `zeroStabilizer_orbitCount` derives
the cardinality from this equivalence by `Nat.card_congr`. The count is therefore
derived from the group's natural action, not an arithmetic placeholder.

`Nat.exists_infinite_primes (max q0 (C+3))` provides the unbounded field family.
Since the actual count is 2, the resulting prime satisfies `count+C<p`.

## Limits and verification status

The construction is standard group theory; a new Lean proof is not a new
mathematical discovery. Source eligibility and upstream solved/PR coverage are
owned by the manager and were unknown at dispatch. The worker claims only a
complete source-bound refutation candidate with a successful development compile.
Independent semantic review and the deterministic package gate remain separate.

The final direct development compile exited 0 with no warnings and printed
only `propext`, `Classical.choice`, and `Quot.sound` for the main results. It
did not run or modify the manager's checker. Earlier failed builds are retained
with actual exits and are not certificates for the final source.
