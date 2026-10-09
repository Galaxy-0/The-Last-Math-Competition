# Disproof of conjecture 00000002751

For A = B = Q, the actual tensor algebra Q tensor_Q Q is algebra-isomorphic
to Q. Each actual multilinear evaluation image has dimension 1, giving PI
exponent 1 for the factors and tensor algebra. The asserted sum is 2.

The complete report is proof.tex with compiled proof.pdf. The Lean 4.19.0
project is lean/, pinned to Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
Reproduce: cd lean; lake update; lake build. Report: tectonic proof.tex.

Validation: the full final lake build passed on the first attempt, with
all eight printed audits using only propext, Classical.choice and
Quot.sound. The PDF compiled and its final single page was rendered and
visually inspected after repairing the draft title layout. Local package
junctions and build outputs are ignored and excluded from the submission.
