# Verification

Run `lake build` in `lean/` using Lean 4.19.0. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b; the manifest records public transitive pins. Local cache junctions are ignored.

The channel is a complex matrix linear map. Complete positivity is proved by identifying every finite ancillary amplification with two positive Kraus terms. The Petz formula at alpha = 1/2 uses canonical positive square roots, evaluated via positivity and square-root uniqueness. The overlap is exactly 24/25, so the logarithm is finite and the divergence positive. Both states are fixed, yielding equality without an assumption.

The reference state's range is the whole complex plane. A killed nonzero matrix proves the channel is not injective and hence not unitary conjugation. A full-rank output cannot fit into one line; this is proved with actual vector ranges. The final theorem assembles all counterexample properties. Only standard logical axioms appear in the printed audits; no proof placeholders, custom axioms, native-decision shortcuts or unsafe code occur.

The PDF was compiled using existing Tectonic after the built-in compiler's known platform-directory failure. Every rendered page was visually inspected. The report explicitly distinguishes pairwise equality from a global all-pairs isometry.
