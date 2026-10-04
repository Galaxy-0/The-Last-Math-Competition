# Verification

- Lean 4.19.0; Mathlib pin c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full `lake build` succeeded: 2080 targets, no warnings. Development errors were corrected before this final successful build.
- Ten printed axiom audits cover infinite dimension, actual scalar kernels/ranges, Fredholm membership, zero index, failure of Fredholmness at zero, the full essential-spectrum formula, actual connected-component membership, and the classification counterexample. All use only propext, Classical.choice and Quot.sound.
- The submitted proof contains no sorry, admit, native_decide, custom axioms or unsafe definitions.
- The ambient space is genuine complex l², not an assumed infinite-dimensional placeholder. The Hilbert basis proves infinite dimension. Fredholm is the complete closed-range/finite-kernel/finite-cokernel predicate; essential spectrum is its failure for A-zI. Actual scalar operators are classified directly, and a continuous Path in the Fredholm subtype establishes connectedComponent membership.
- The final one-page PDF was compiled once using existing Tectonic and inspected in full. No layout or clipping defects were found. The editable source was opened in the built-in editor; its compiler had the known platform-directory failure, so the existing Tectonic fallback was used.
- No shared-cache extension, auxiliary executable, independent review or repeated successful build was needed. Local cache junctions and build files are ignored; public pinned configuration is submitted.
