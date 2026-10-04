# Disproof of 00000008480

The one-point compact ergodic probability system with identity map, continuous observable `f=0`, and unbounded driver `h_i=i` has optimized averages `(n-1)/2` for positive n. Their ratio to n tends to 1/2, so their growth is not sublinear.

The formalization also allows every fixed sliding-window origin k. It proves that the actual supremum over initial states is `k+(n-1)/2`, using genuine finite sums, map iterates, and `sSup` of the actual value set. For each fixed k, the ratio tends to 1/2, and Mathlib's `IsLittleO` condition relative to n is false.

- `report.tex`, `report.pdf`: complete mathematical proof, exact scope and formal correspondence.
- `lean/Main.lean`: actual compact/continuous/ergodic probability system, unbounded driver, singleton supremum computation, sum identities, limit and not-little-o proof.
- `lean/lakefile.lean`, `lean/lake-manifest.json`, `lean/lean-toolchain`: pinned public Lean 4.19.0 / Mathlib configuration.
- `VERIFICATION.md`: observed checks and eligibility evidence.

From `lean/`, run `lake update`, `lake exe cache get`, `lake build`, then `lake env lean Main.lean -DwarningAsError=true`. Six principal dependency audits are printed; all use only standard logical axioms. Ignored local cache junctions and build products are not committed.

Both source versions claim sublinear growth for unbounded driving without a growth/cancellation restriction. This disproof addresses that universal conjunct. The supremum is over initial states for a fixed finite window; the origin k is fixed before taking the limit in n. A different supremum over all possible window origins is not substituted for this operation.

The built-in source editor/compiler was attempted but returned the environment's platform-directory failure. Tectonic produced the delivered PDF, and both final pages were visually checked.
