# Verification

- Lean 4.19.0, Mathlib pin c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full `lake build` succeeded: 1718 targets, no warnings. An initial reserved-identifier error was corrected before the successful build.
- Twelve printed axiom audits cover both maximal monotone operators, cocoercivity, absence of zeros, both genuine resolvent equations, exact stages and orbit, absence of weak limits for iterates and both shadows, and emptiness/nonemptiness failure of the actual convergence domain. All use only propext, Classical.choice and Quot.sound.
- The submitted proof contains no sorry, admit, native_decide, custom axioms or unsafe definitions.
- Maximality quantifies over arbitrary set-valued monotone extensions. The real Hilbert inner product is multiplication. Resolvents are actual continuous linear identity maps and are proved to satisfy the set-valued inverse equation. The orbit is the actual function iterate of the full Davis-Yin stage map, rather than an independently postulated recurrence.
- Weak convergence is tested against all continuous real linear functionals. The identity functional and the nonzero successive difference disprove it. Every positive step/relaxation and every initial state are covered; both shadows are also checked. The existential-initial-state convergence domain is proved equal to the empty set.
- One Tectonic compile produced the final 39104-byte two-page PDF. Both pages were visually checked without clipping or layout defects. The source was opened in the built-in editor; its known platform-directory compiler failure required the existing Tectonic fallback.
- No shared cache extension, auxiliary executable, independent review or repeated successful build was needed. Public dependency pins are included; local build files and cache junctions are ignored.
