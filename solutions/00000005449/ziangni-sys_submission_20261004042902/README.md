# Counterexample to conjecture 00000005449

The standard commutativity spot-check draws two independent uniform group elements and detects noncommutativity precisely when their products differ. On the actual symmetry group of the square, 24 of 64 ordered pairs do not commute, so a single check detects with probability 3/8, below the asserted 1/2.

Lean uses Mathlib's actual DihedralGroup 4 group operations. It verifies a noncommuting witness, actual group and pair cardinalities, full commuting/noncommuting pair counts, normalized independent uniform rational sampling weights, and the probability obtained by summing those weights over the actual detection event.

Only the single-check lower-bound clause is refuted. No claim is made about unspecified alternative checking algorithms or the separate automorphism correction clauses.

## Reproduction

Lean 4.19.0 with pinned Mathlib:

    cd lean
    lake update
    lake exe cache get Mathlib/GroupTheory/SpecificGroups/Dihedral.lean Mathlib/Tactic/NormNum.lean
    lake build
    lake env lean Main.lean -DwarningAsError=true

Compile report.tex with Tectonic. See VERIFICATION.md.
