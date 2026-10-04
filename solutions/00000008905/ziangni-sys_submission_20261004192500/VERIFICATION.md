# Verification

- Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full lake build passed 1558 targets without warnings after development computation and simplification repairs.
- Ten printed axiom audits use only propext, Classical.choice, and Quot.sound.
- No sorry, admit, native_decide, unsafe declarations, or custom axioms.
- Formal coverage: actual SimpleGraph objects on six vertices; explicit adjacency matrix identities; rational matrix certificates T*U=1 and A_G*T=T*A_H; generic determinant argument giving equality of characteristic polynomials; transfer to actual complex adjacency matrices and equality of full polynomial root multisets; equivalence between all adjacency-preserving finite functions and the actual SimpleGraph.Hom type; exact homomorphism counts 20 and 16; impossibility of any reconstruction function on either characteristic polynomials or eigenvalue multisets.
- Matrix certificates use norm_num; finite homomorphism enumeration uses kernel-checked decide. Auxiliary scratch scripts only helped write constants; the submitted Lean proof independently checks every constant, and no script is needed to reproduce the proof.
- The ordinary graph-homomorphism interpretation of the terse source is stated explicitly. Closed-walk counts and restricted regular-graph claims are not challenged.
- Built-in LaTeX compilation encountered the known platform-directory error. Existing Tectonic compiled the report; the formal-method paragraph was updated when the proof switched to an invertible intertwiner, then the final PDF was compiled and both pages visually checked without clipping. PDF size: 41394 bytes.
