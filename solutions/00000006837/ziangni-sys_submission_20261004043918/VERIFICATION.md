# Verification

## Scope

The source describes orthogonal complements pairing adjoint invariant subspaces. The proof establishes the standard bounded Hilbert-space interpretation over both real and complex fields, in arbitrary dimension. The forward direction applies to every linear subspace. The converse and full order-reversing bijection apply to closed invariant subspaces, the standard invariant-lattice convention. No converse for a nonclosed subspace is asserted: its double orthogonal complement is its closure.

## Lean

Lean 4.19.0, Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b, publicly pinned. The single imported module is Mathlib.Analysis.InnerProductSpace.Adjoint.

- Fresh project lake build completed successfully, 2085 jobs.
- Direct whole-source lake env lean Main.lean -DwarningAsError=true exited 0.
- Actual objects: continuous linear operator and its Mathlib adjoint, complete inner-product space, submodules, orthogonal complements, and topological closedness.
- Invariant is defined as actual preservation: forall x in U, A x in U.
- orthogonal_invariant proves the arbitrary-subspace forward direction directly from the adjoint inner-product identity.
- closed_invariant_iff proves both directions using the actual double-adjoint and double-orthogonal identities.
- adjointCorrespondence bundles the forward/inverse maps and proves both inverse laws for all closed invariant subspaces.
- correspondence_reverses_order proves inclusion iff reverse inclusion of their images.
- All four audited results use only propext, Classical.choice, Quot.sound. No sorry, admit, native_decide, or additional axioms.

Targeted shared Adjoint cache extension completed successfully (3 missing files; 2072 closure files). Cache writer released; pinned versions unchanged. Ignored junctions are local build conveniences only. No lake clean used.

## PDF and repository

PDF artifact creation marker performed. Native editor opened and compilation attempted; native compiler returned the known platform-directory lookup failure. Tectonic compiled final report successfully, without overfull-box warnings. Poppler confirms one A4 page, 26695 bytes, PDF1.5. Complete final page rendered at120dpi and inspected: readable formulas, correct margins, no clipping/overlap/orphan page.

Only this submission directory is committed. All text files use LF. Public project config uses Git-pinned dependencies; caches/build products are ignored. Staged git diff --check passed.
