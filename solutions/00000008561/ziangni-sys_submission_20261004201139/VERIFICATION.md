# Verification

- Lean 4.19.0; Mathlib pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full `lake build` succeeded: 2,588 targets, no warnings. Development elaboration errors were corrected before this final successful build.
- Ten printed axiom audits cover nonnormality, the actual inverse diagonalization, upper/lower operator norms, every eigenbasis condition number, its infimum, the actual resolvent estimate, pseudospectrum containment, finite area, and the strict failure of the conjectured area bound. All use only propext, Classical.choice and Quot.sound.
- No sorry, admit, native_decide, custom axioms or unsafe definitions occur in the submitted proof.
- The matrices act on the actual Euclidean complex Hilbert space through an algebra equivalence preserving adjoints. EigenbasisPair requires actual two-sided inverses and actual diagonalization; the nonempty condition-number set is not assumed. The infimum ranges over all ordered diagonalizers, without fixing an eigenvector scaling.
- `pseudo` is the union of Mathlib's actual spectrum and the actual resolvent superlevel set at epsilon 10. The source's resolvent-only set is contained in it. Its genuine complex Lebesgue measure is finite and at most 196 pi, whereas the proposed lower bound is at least 900 pi.
- The final one-page PDF was compiled once with existing Tectonic and visually inspected in full. No clipping or layout defects were found. The built-in compiler was unavailable because of its platform directory error; its editable source was preserved and opened in the editor.
- No auxiliary executable, independent review, or repeated successful Lean build was needed. Public dependency pins are included; local cache links and build artifacts are ignored.
