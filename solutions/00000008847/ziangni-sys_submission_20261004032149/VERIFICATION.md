# Verification evidence

Verified on 2026-10-04 with Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Definitions and full semantic scope

The theorem is generic over any real inner-product space E. It requires
neither completeness nor continuity. Set-valued maps are actual functions
`E -> Set E`; empty values and empty domains are allowed.

- `graph A` is `{(x,u) | u in A(x)}`.
- `ofGraph s x` is `{u | (x,u) in s}`.
- `graph_ofGraph` and `ofGraph_graph` prove both inverse identities.
- `IsMonotoneGraph` is the pairwise inequality
  `0 <= inner (x-y) (u-v)` on graph points.
- `monotone_iff` proves agreement with the pointwise operator definition.
- `Extends A B` is pointwise inclusion of values; `graph_subset_iff`
  proves equivalence to graph inclusion.
- `IsMaximalMonotone A` means A is monotone and every monotone extension
  of A equals A.

`monotone_sUnion` proves that the union of any inclusion chain of monotone
graphs is monotone. It extracts containing graphs for two arbitrary
points and uses comparability to place them together. This also holds
for the empty chain, whose union has no points.

`exists_maximal_graph` applies the standard library theorem
`zorn_subset_nonempty` with the prescribed initial graph as its seed.
Thus the result explicitly contains that graph, and the nonempty-chain
version does not lose the initial extension condition. In the equivalent
poset of extensions described in the report, the initial graph itself
is an upper bound for the empty chain.

`maximal_graph_iff` proves equivalence between Mathlib's order-theoretic
`Maximal` predicate on monotone graphs and `IsMaximalMonotone` on maps.
`exists_maximal_extension` uses the graph/map bijection to obtain the
operator. The final theorem combines BOTH assertions of the original.

## Lean checks

```text
lake build
lake env lean Main.lean
```

Both exited with code 0. The local project build directory was initially
absent; the dependency cache matches the pinned Mathlib revision. The
full build printed `Built Main` and `Build completed successfully.`
The direct file check printed the audit:

```text
'MaximalMonotone8847.conjecture_00000008847' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There are no additional axioms, `sorry`, `admit`, or `native_decide` in
the proof. Classical choice is expected for this Zorn argument. All graph
and inner-product statements are Lean terms checked by the kernel.

## Report checks

The PDF artifact marker was run before authoring. The built-in editor
was opened and compilation attempted, returning the known platform-
directory lookup error. The actual PDF was successfully built using
Tectonic and rendered with Poppler. Both pages were inspected in full
for legibility, complete content, spacing, and absence of clipping or
overlap. The final compilation has no overfull/underfull box warnings.
Tectonic prints a nonfatal Fontconfig diagnostic, with correctly embedded
Latin Modern fonts and correct visual output.

No auxiliary numerical program is required.
