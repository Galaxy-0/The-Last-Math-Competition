# Proof of Conjecture 00000008847

Every set-valued monotone operator on a real inner-product space has a
maximal monotone extension. Maximal monotone operators correspond exactly
to maximal elements in the inclusion order on monotone graphs. This
proves both clauses of the original conjecture, and in particular covers
real Hilbert spaces. Completeness is not needed.

The proof uses Zorn's lemma. A union of a chain of monotone graphs is
monotone because any two points of the union lie together in one member
of the chain. The original graph provides the seed for the extension
argument. Explicit inverse constructions between graphs and set-valued
maps transfer the maximality result back to operators.

## Files

- `report.tex` and `report.pdf`: full proof, definitions, and formal correspondence.
- `lean/`: Lean 4.19.0 project with a pinned Mathlib dependency.
- `VERIFICATION.md`: exact theorem scope and verification evidence.

## Reproduction

With the pinned toolchain installed, run from `lean`:

```sh
lake exe cache get
lake build
lake env lean Main.lean
```

The manifest uses public Git revisions and no local paths. Local cache
links and build products are ignored. Use a short checkout path on
Windows to avoid path-length failures in Mathlib imports.

Compile the report from this submission directory with:

```sh
tectonic -X compile report.tex
```

The final theorem is
`MaximalMonotone8847.conjecture_00000008847`. It combines existence of a
maximal extension with the exact graph-order characterization. The
definitions use actual subsets of a product space and the ordinary
real inner-product monotonicity inequality. The proof uses classical
choice through Zorn's lemma; it does not assert uniqueness or an effective
algorithm for choosing a maximal extension.
