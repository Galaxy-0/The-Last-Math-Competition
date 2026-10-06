# Verification record

Verified on 2026-10-06 using Lean 4.33.1 and pinned Mathlib. The root agent
read the complete source and independently built the project, including
the explicit identification of iterative doubling with multiplication by
`2^n`. The cardinal-valued capstone uses Mathlib's standard `StrictAnti`,
not a separately postulated numeric or certificate predicate.

The printed audits of `quotient0_card`, `quotient1_card`,
`cardinalStrictAnti_fails`, and
`counterexample_fails_strict_cardinal_decrease` contain only
`[propext, Classical.choice, Quot.sound]`.

Actual coordinate-group checks cover just eight elements. The code has no
unfinished proofs, native evaluation, custom axioms, or long brute force.
The report source compiles with Tectonic and the desktop LaTeX compiler;
the exported one-page PDF is rendered and visually inspected.
