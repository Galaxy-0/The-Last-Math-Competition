# Proof of conjecture 00000006406

Complement preserves the actual symmetric-difference set: Aᶜ ∆ Bᶜ = A ∆ B. Thus it preserves every distance obtained by assigning a fixed size to that set. Double complementation is the identity, so complement and its twofold composition are involutions.

Lean proves the arbitrary-set identity, De Morgan identities, arbitrary-functional distance equality, and a Mathlib Isometry theorem for pseudometrics defined by symmetric difference. It also proves an unconditional concrete Hamming-metric isometry on finite Boolean characteristic words.

## Reproduction

Lean 4.19.0, pinned Mathlib:

    cd lean
    lake update
    lake exe cache get Mathlib/Data/Set/SymmDiff.lean Mathlib/Topology/MetricSpace/Isometry.lean Mathlib/InformationTheory/Hamming.lean
    lake build
    lake env lean Main.lean

Compile report.tex with Tectonic. See VERIFICATION.md.
