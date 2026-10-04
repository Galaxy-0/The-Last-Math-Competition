# Verification evidence

Verified on 2026-10-04 with Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## General scope and actual definitions

The general theorem has arbitrary source X and target Y and an arbitrary
predicate C on pairs of points in X × Y. No algebraic, topological,
reflexivity, symmetry, or transitivity assumption is imposed on C.
Set-valued maps are actual functions `X -> Set Y`.

- `graph A` is `{(x,u) | u in A(x)}`.
- `ofGraph s x` is `{u | (x,u) in s}`.
- `graph_ofGraph` and `ofGraph_graph` prove both inverse identities.
- `IsAdmissibleGraph C s` is `forall p in s, forall q in s, C p q`.
- `admissible_iff` exposes the corresponding pointwise map property.
- `Extends A B` is pointwise inclusion, and `graph_subset_iff` proves
  its exact equivalence to graph inclusion.
- `IsMaximalAdmissible C A` means A is admissible and every admissible
  extension B equals A.

`admissible_sUnion` proves the chain-union lemma for arbitrary C. Two
points in the union lie together in one comparable chain member. The
empty chain has empty union, which is vacuously admissible.
`exists_maximal_graph` uses `zorn_subset_nonempty`, supplying the original
admissible graph as seed. In the equivalent poset of extensions described
in the report, that seed bounds the empty chain. No extension hypothesis
or maximality conclusion is assumed.

`maximal_graph_iff` proves BOTH directions between Mathlib's `Maximal`
predicate on admissible graphs and no proper admissible map extensions.
`exists_maximal_extension` transfers the seeded graph theorem to maps.
The general `conjecture_00000008847` combines both original clauses.

## Actual standard monotonicity instances

`InnerProduct.compatible` uses the real inner product of x-y and u-v.
`InnerProduct.monotone_iff` identifies admissibility with ordinary
inner-product monotonicity. `InnerProduct.result` specializes BOTH
conclusions, for every real inner-product space.

`Duality.compatible` takes graph points in E × (E ->L[Real] Real), where
E is an arbitrary real normed space. Its predicate is the inequality
`0 <= (u-v)(x-y)` using the actual continuous linear map subtraction and
evaluation. `Duality.monotone_iff` proves the pointwise correspondence.
`Duality.result` specializes BOTH conclusions. In particular it covers
all real Banach spaces and operators into their continuous duals, without
requiring completeness. The general theorem is not restricted to these
two instances and applies to any other pairwise monotonicity convention.

## Lean verification

```text
lake build
lake env lean Main.lean
```

The revised direct Lean source check exited with code 0 and no warnings.
The revised project build also exited with code 0, rebuilding Main.
All three final audits printed the same standard logical axioms:

```text
'MaximalMonotone8847.conjecture_00000008847' depends on axioms: [propext, Classical.choice, Quot.sound]
'MaximalMonotone8847.InnerProduct.result' depends on axioms: [propext, Classical.choice, Quot.sound]
'MaximalMonotone8847.Duality.result' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There are no additional axioms, `sorry`, `admit`, or `native_decide` in
the proof. Classical choice is expected for the Zorn argument. All
pairwise graph statements and the concrete monotonicity instances are
kernel checked. No dependency cache version was changed for the revision.

## Revised PDF verification

The PDF edit marker was run before revising the report. The built-in
editor remains on the same source. Its compiler was attempted and
returned the known platform-directory lookup error. Tectonic successfully
built the revised three-page PDF; all three pages were rendered using
Poppler and inspected in full. The final compile has no overfull or
underfull box warnings and no missing, clipped, or overlapping content.
Tectonic's nonfatal Fontconfig diagnostic does not affect the embedded
Latin Modern fonts or the visual output.

No auxiliary numerical program is required.
