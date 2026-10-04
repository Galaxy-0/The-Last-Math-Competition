# Verification

- Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full `lake build` passed 909 targets without warnings after development import/specialization fixes.
- Eleven printed axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
- No sorry, admit, native_decide, unsafe declarations, or custom axioms.
- Formal coverage: actual congestion loads, latency costs, every unilateral profile update, full Nash conditions, existence for arbitrary positive constant-latency vectors on nonempty finite player/resource sets, exact global optimum via sInf, entire equilibrium ratio set, exact PoA supremum, and the sharp class-level supremum.
- The two-player/two-resource example belongs to a spectrum over all positive nondecreasing latency functions admitting a Nash profile. All probability weights on its profiles have expected social cost 2. The target is the claimed first spectrum value, with no exclusion of PoA 1 in the source.
- Built-in LaTeX compilation encountered the known platform-directory error. Existing Tectonic compiled the final PDF once; both pages were rendered and visually checked without clipping. PDF size: 39404 bytes.
