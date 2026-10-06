# Conjecture 00000001952: rank-one disproof

The source assertion gives no lower-rank restriction besides the usual
positive rank of a free group. At n=1 the claimed minimum finite-index
subgroup index is `2^1 * choose(1,2) = 0`. Actual finite subgroup indices
are positive because finite coset spaces are nonempty.

The Lean code constructs `Out(F_n)` as
`MulAut (FreeGroup (Fin n)) / range(MulAut.conj)` and proves that the
conjugation image is normal. It does not replace Out by an unspecified
or hardcoded finite group and does not need an isomorphism Out(F_1)=C_2.

The minimum definition has both an actual subgroup attaining the value
and minimality over all eligible subgroups. If the whole group is eligible,
the actual minimum is 1; Lean proves this for Out(F_1). If the minimum is
restricted to proper subgroups, any attained finite minimum is still
positive, so the conjectured value 0 is impossible in that convention too.
The equivalence between a finite coset space and nonzero subgroup index
is explicitly proved from Mathlib, rather than an assumed numeric premise.

The source's further kernel-of-action clause does not change the failed
value of the asserted minimum. This submission treats the conjecture as
written. It does not claim to handle a different version restricting n>=2
or n>=3, nor compute the proper minimum via Out(F_1)=C_2.

## Prior error

Closed PR #240 proposed the determinant-action kernel at rank three.
Its Lean theorem was just numeric index comparisons, with the relevant
outer automorphism group, determinant action, subgroup, and coset indices
absent from the formal development. The reviewer also observed that the
problem itself already allows action kernels among smaller indices.
The new proof uses the actual Out quotient and actual finite subgroup
indices at rank one, not that previous argument or numeric certificate.

## Reproduction

In `lean/`, run `lake update`, `lake exe cache get`, and `lake build`.
Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` are pinned, with a dependency
lockfile. The five printed theorem audits use only `propext`,
`Classical.choice`, and `Quot.sound`. There are no unfinished proofs,
native evaluations, or additional axioms. The report source and PDF are
`solution.tex` and `solution.pdf`.
