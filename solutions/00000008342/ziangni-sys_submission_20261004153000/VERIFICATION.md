# Verification

- Lean 4.19.0 and Mathlib pin `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Final full `lake build` passed, 1803 targets. Eight axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`; no final warnings.
- Actual integer triples, sphere equation, maximum absolute coordinate, and real sSup of all point heights are defined. All-point bounds and a genuine attaining point establish the exact supremum.
- Square parameters tend to infinity. Exact positive-square ratios and their limits disprove both the stated sqrt(m/3) formula and its extra-one-third reading. The report explicitly addresses maximal height rather than typical or average height.
- No proof gaps, custom axioms, unsafe declarations, or native decision shortcuts. No auxiliary computational program is required.
- Tectonic produced a 33080-byte, two-page A4 PDF; both rendered pages were visually checked. The built-in compiler returned the known platform-directory failure; Tectonic completed with the environment's harmless fontconfig warning.
- Public dependency pins are committed. Ignored local cache junctions and build products are excluded. No new cache extension was needed.
