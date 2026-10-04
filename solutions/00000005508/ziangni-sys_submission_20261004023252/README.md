# Disproof of conjecture 00000005508

A one-station capacity network disproves the logarithmic bound on bottleneck multiplicity: its bottleneck set has cardinality 1, whereas log(1) = 0, in every genuine logarithm base.

The source explicitly equates the tied-bottleneck count with minimum multiplicity, so a unique minimum contributes one. The report also gives a two-station comparison for the conventional logarithm bases.

The Lean project defines positive service capacities and traffic coefficients, saturation, first bottlenecks, and the actual finite bottleneck set. Its final theorem negates the universal logarithmic bound, a necessary clause of the source conjunction.

## Reproduction

With Lean 4.19.0, run these commands from the lean directory:

    lake update
    lake exe cache get Mathlib/Analysis/SpecialFunctions/Log/Basic.lean Mathlib/Data/Finset/Card.lean
    lake build
    lake env lean Main.lean

The manifest pins all dependency revisions, including Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.

Compile report.tex with Tectonic. Observed validation results are recorded in VERIFICATION.md.
