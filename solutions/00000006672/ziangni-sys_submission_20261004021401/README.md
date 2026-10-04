# Disproof of conjecture 00000006672

The real 2×2 transportation polytope with all four margins equal to one has the identity matrix as an extreme point. Its positive-support graph contains just `r0--c0` and `r1--c1`, so it is disconnected and is not a spanning tree. The Chinese conjecture explicitly describes support trees; no nondegeneracy hypothesis is present. Adding a zero basic variable to form a tree basis does not change positive support.

## Contents

- `report.tex`, `report.pdf`: complete elementary mathematical argument and interpretation of the statement.
- `lean/Main.lean`: real-matrix proof using Mathlib's standard extreme-point and tree definitions.
- `lean/lakefile.lean`, `lean/lean-toolchain`, `lean/lake-manifest.json`: pinned, portable project metadata.
- `verification/lean-build.txt`: successful standalone project build output.
- `verification/axioms.txt`: direct Lean source check and final theorem axiom audit.
- `verification/report.log`: final TeX compilation log.
- `verification/notes.md`: exact verification procedure, scope, and local environment details.

## Reproduce the formal proof

Install Lean 4 using elan, then run from `lean/`:

```sh
lake exe cache get Mathlib.Data.Real.Basic Mathlib.Analysis.Convex.Extreme Mathlib.Combinatorics.SimpleGraph.Acyclic
lake build
lake env lean Main.lean
```

The checked-in toolchain selects Lean **4.19.0**. Mathlib is pinned to commit **c44e0c8ee63ca166450922a373c7409c5d26b00b** (v4.19.0); the manifest also pins every transitive dependency. A fresh run obtains the public Git dependencies. No local absolute paths occur in the project metadata. The cache download is an optimization: ordinary Lake compilation can build dependencies from source instead.

On Windows, use a short project path to avoid the traditional 260-character path limit in dependency filenames. For example, map an unused drive to this submission's `lean` directory using `subst T: "<absolute path to lean>"`, run the commands from `T:\`, then leave that directory and remove only the drive mapping using `subst T: /D`.

Expected final source-check output:

```text
'Transport.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'Transport.not_all_vertices_have_tree_support' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard logical foundations. There are no added axioms, admitted proof terms, or native decision shortcuts in the submission.

## Formal statement and coverage

`Mat := Bool → Bool → ℝ`, with Boolean indices for the two rows and two columns. `P` is exactly the real nonnegative matrix set with all row and column sums equal to one. `diagonal_extreme` proves `diagonal ∈ P.extremePoints ℝ`, quantifying over arbitrary feasible **real** endpoints and arbitrary positive **real** weights summing to one. No rational/integer restriction or unproved scalar bridge is used.

`support X` is the actual bipartite positive-support `SimpleGraph` on the four row and column vertices. `support_walk_preserves_index` uses induction on Mathlib walks; `support_disconnected` and `support_not_tree` then establish the graph obstruction. `counterexample` provides the witness, and `not_all_vertices_have_tree_support` negates the universal support-tree claim for this transportation polytope.

The conjecture is a conjunction. Falsifying its first clause suffices; this submission does not reinterpret its vague capacity clause or contest the matrix-tree theorem. No auxiliary computational verifier is necessary for this symbolic proof.

## Rebuild the report

```sh
tectonic report.tex --keep-logs
```

A standard LaTeX installation with the listed packages also suffices. The supplied PDF has two pages and was rendered and visually inspected in full.
