# Verification evidence

Date: 2026-10-04. Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.

## Semantics

Both source languages assert nonnegativity of superdimensions without restricting parity or excluding trivial representations. The standard superdimension is even dimension minus odd dimension, as an integer.

The formal model uses actual complex vector spaces and submodules. A SuperSpace requires disjoint grading subspaces with supremum equal to the whole space. The fixed acting algebra is the complex abelian line in even degree with zero odd part. Its bilinear zero bracket is an actual nested LinearMap, and graded skew/Jacobi laws reduce to explicitly checked zero identities. A SuperRepresentation records a nested linear action, the bracket commutator law and preservation of both parity subspaces. These are all required representation axioms for this purely even algebra.

The witness uses even submodule bottom, odd submodule top and action zero. Its finrank dimensions are proved 0 and 1; neither is hypothesized. The final theorem proves the integer superdimension is negative in a legitimate restricted family of the original domain.

## Checks

- Fresh project lake build passed, 1728 targets, no tactic warnings.
- Direct lake env lean Main.lean passed.
- Axiom audits for bracket Jacobi, both actual dimensions and final negation list only propext, Classical.choice and Quot.sound.
- No sorry, admit, native_decide or new axiom declarations.
- Ignored local dependency junctions and build outputs are excluded; public manifest uses pinned Git revisions only.
- Built-in source editor opened. Built-in compiler returned its known platform-directory failure.
- Tectonic successfully compiled the final one-page A4 PDF with no overfull-box or reference warnings.
- Entire final PDF page rendered by Poppler and visually inspected; no clipping, overlap or missing symbols.
- No auxiliary code or computational assumptions required.
- git diff --check passed, and the only committed paths are in this personal submission.
