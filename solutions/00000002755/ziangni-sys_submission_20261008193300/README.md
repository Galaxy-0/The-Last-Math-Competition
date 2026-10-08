# Disproof of conjecture 00000002755

The scalar algebra Q has actual multilinear evaluation image dimension 1
in every degree and therefore PI exponent 1. Its index-one Capelli
polynomial X fails at 1. This refutes the claimed equivalence at n = 1.
The index counts alternating variables; the full convention is in proof.tex.

Files: proof.tex, compiled proof.pdf, and the pinned Lean project in lean/.
Reproduce with Lean 4.19.0: cd lean; lake update; lake build.
Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b.
For the report use tectonic proof.tex.

Validation: one successful full final lake build. Audits printed in
Main.lean use only propext, Classical.choice and Quot.sound. The report
compiled with Tectonic and its single page was rendered and visually
inspected. The evaluation map, its kernel quotient equivalence and
codimensions are constructed, rather than assigning a constant sequence.
Local dependency junctions and build products are ignored and not submitted.
