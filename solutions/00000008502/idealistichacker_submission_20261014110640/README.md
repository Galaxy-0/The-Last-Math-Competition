# Conjecture 00000008502: a dimension-zero Picard-Vessiot counterexample

The exact second-order dimension spectrum {1,2,3,4} in the bilingual source
is false. Take the characteristic-zero differential field K = Complex(t),
with D = d/dt, a = 0, fundamental matrix [[1,t],[0,1]], and PV field L = K.
The actual differential Galois group fixes every element and is trivial.
Its fundamental-matrix representation U^(-1)*sigma(U) is the identity.
The genuine represented Zariski closure is the identity point, whose actual
polynomial coordinate quotient is isomorphic to Complex, with Krull dimension
zero. Thus zero is an admissible dimension outside the asserted exact spectrum.

The standard PV assumptions are proved for this concrete instance: genuine
rational-function derivation, constants exactly Complex, algebraically closed
constant field, invertible fundamental matrix, generated self-extension and
no new constants. The generated PV ring is the base field and is differentially
simple. The zero coefficient does not turn the monic order-two equation into
an order-one equation. No proper-extension restriction occurs in the source.

## Formal correspondence

- RationalDerivative.lean: actual RatFunc quotient derivative, representation
  independence, addition and Leibniz laws, D(t)=1, exact constant field.
- DifferentialMatrix.lean: actual matrices and base-fixing automorphisms.
- PointClosure.lean: polynomial zero loci, standard induced Zariski topology,
  closure, GL2 determinant-inverse coordinates, evaluation kernel quotient and
  Krull dimension. Algebraic dimension is not defined by group cardinality.
- ConcretePV.lean: genuine PV field data and correct matrix representation,
  actual represented closure dimension zero, closed exact-spectrum negation.
- Check.lean: all 76 public theorem types and transitive axioms.

Only the necessary exact-spectrum clause is refuted. No full corrected
classification, general representation-existence theorem or separate refutation
of the source's n-squared upper bound and equality criterion is claimed.
The precise original Git blob is preserved in source.md.

## Reproduction and trust

Lean 4.33.1 and Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474
are pinned, with all nine Git dependencies fixed by lake-manifest.json.
Run python reproduce.py --lake <Lake executable> --repo <source checkout>.
Explicit --skip-update is the exact offline dependency-audit mode; it does
not waive source, physical checkout, clean authored build, theorem inventory
or axiom checks. Only own-project generated build outputs are rebuilt;
existing dependency caches are reused and remain a disclosed trust input.

Only propext, Classical.choice and Quot.sound are allowed in the kernel audit.
Finite exact rational regression checks support reproduction but do not replace
the universal Lean proofs. No full-dependency clean or empty-machine bootstrap
is claimed. Installed compiler and fixed library remain trusted infrastructure.

This is an AI-assisted submission by idealistichacker, without an affiliation,
first-solver, human endorsement, acceptance, ranking or award claim. A different
AI-agent frozen-package review is separate from author compilation and from
upstream maintainer review. Publication occurs only after all per-PR gates.
