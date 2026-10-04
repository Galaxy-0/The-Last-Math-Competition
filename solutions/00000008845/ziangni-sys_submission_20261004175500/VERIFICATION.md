# Verification

- Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full `lake build` passed 2085 targets without warnings after development projection/rewriting fixes.
- Twelve printed axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
- No sorry, admit, native_decide, unsafe declarations, or custom axioms.
- Formal coverage: actual Hilbert-line continuous linear identity and adjoint; joint quadratic convexity, continuity/lower semicontinuity and properness; representation of every product-space dual functional; full Fenchel sSup with actual maximizing point; self-duality under primal/dual exchange; generated equality graph; actual maximal monotonicity and inverse graph; no antisymmetric graph extension and no dense-domain antisymmetric restriction.
- The two extension directions are treated independently. Antisymmetry uses the actual real inner-product skew identity, matching antisymmetric bilinear forms. Self-dual Lagrangian, self-adjointness and inverse-graph invariance are individually proved, not conflated as generally equivalent notions.
- Built-in LaTeX compilation encountered the known platform-directory error. Existing Tectonic compiled the final PDF once; both pages were rendered and visually checked without clipping. PDF size: 39203 bytes.
