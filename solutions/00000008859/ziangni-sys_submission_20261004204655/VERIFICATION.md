# Verification

- Lean 4.19.0, Mathlib pin c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full `lake build` succeeded: 1718 targets, no warnings. Development errors were corrected before this final successful build.
- Ten printed axiom audits cover full maximal monotonicity, unique zero, actual resolvent equation, two-sided inverse, actual inverse operator norm, first update, exact inertial recurrence, geometric bound, all-initials convergence and failure of the asserted IsLUB. All use only propext, Classical.choice and Quot.sound.
- The submitted proof contains no sorry, admit, native_decide, custom axioms or unsafe definitions.
- The operators are actual bounded continuous linear maps on R. Maximality quantifies over all set-valued monotone extensions. The weighted state is an actual R x R orbit in the genuine product norm; its first coordinate is proved to satisfy the standard inertia recurrence for every initial pair and every inertia parameter.
- The counterexample beta=1/2 lies in the conventional range [0,1). It converges for every initial pair, so the proposed value 1/10 fails the upper-bound property, without assuming boundedness or attainment of the true supremum.
- One Tectonic compile produced the final 37279-byte two-page PDF. Both pages were visually checked without clipping or layout defects. The source was opened in the built-in editor; its known platform-directory compiler failure required the existing Tectonic fallback.
- No shared cache extension, auxiliary executable, independent review or repeated successful build was needed. Public dependency pins are included; local build files and cache junctions are ignored.
