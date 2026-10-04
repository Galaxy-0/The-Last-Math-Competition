# Verification evidence

Date:2026-10-04. Lean4.19.0; Mathlib pinned c44e0c8ee63ca166450922a373c7409c5d26b00b.

## Scope and semantics

The source claims complement is always an isometry of the symmetric-difference metric and that composition of complements is involutive, via De Morgan. The formal proof applies to arbitrary universes and arbitrary sets: the actual symmetric-difference set is unchanged by complementation. Any size functional of that set therefore yields the same distance. The actual Isometry theorem's only structural hypothesis is the definition of a symmetric-difference metric; it does not assume distance preservation by complement.

Both De Morgan identities, double complementation, complement involutivity, equality of its twofold composition with the identity and involutivity of that composition are proved.

The concrete unconditional Isometry theorem uses the actual Hamming metric on finite Boolean characteristic words. wordSet identifies these words with subsets; bitwise complement is proved to represent set complement, and mismatched coordinates are proved equivalent to symmetric-difference membership. This is the canonical finite counting-distance case.

Complement is relative to a fixed universe. On restricted families it must act within a complement-closed family. Full power sets and all finite Boolean words have this automatically.

## Checks

- Fresh lake build passed,1188targets; direct lake env lean Main.lean passed.
- Axiom audits for set identity, arbitrary distance equality, final conjunction and concrete Isometry list only propext, Classical.choice, Quot.sound.
- No sorry, admit, native_decide or extra axiom declarations.
- Dependency manifest pins public revisions; local junctions and build outputs ignored.
- Built-in editor opened source. Native compiler returned known platform-directory lookup failure; Tectonic successfully compiled the actual PDF.
- Final one-page A4 PDF produced without overfull-box or reference warnings, rendered with Poppler, and visually inspected completely with no clipping or overlap.
- No auxiliary computational code required.
- git diff --check passed; submission scope only personal directory.
