# Verification

- Lean 4.19.0; Mathlib pin `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Final full `lake build` passed, 2268 targets. Eight printed audits use only `propext`, `Classical.choice`, and `Quot.sound`; no warnings in the final build.
- The actual set includes interval membership, irrationality, positive strict errors, and unbounded denominators. The actual factorial Liouville constant is a member at every integer parameter. Its interval membership is proved from Mathlib's partial-sum/tail estimates.
- The dimension is Mathlib's `MeasureTheory.dimH`. Its upper bound by one establishes finiteness before taking its real value. The contradiction is against the real number -1, not a truncated ENNReal cast.
- No proof gaps, native decision shortcuts, custom axioms, or unsafe declarations. No auxiliary computational code is required.
- Tectonic produced the final 45010-byte, one-page A4 PDF; its rendered page was visually checked. The built-in compiler had the known platform-directory error; the existing Tectonic compiler completed with only the environment's harmless fontconfig warning.
- Local ignored dependency junctions reuse the pinned cache; submitted configuration contains public Git pins.
