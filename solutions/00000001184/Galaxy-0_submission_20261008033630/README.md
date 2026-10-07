# Counterexample to TLMC 00000001184

For the genuine finite group of Lie type PSL₂(F₅), eight explicit proper subgroups cover 888 of the 3600 ordered pairs. Therefore the probability that two independent uniform elements generate is at most 2712/3600 = 113/150, strictly less than the asserted 19/25 bound at q=5.

The proof uses canonical determinant-one matrices modulo simultaneous sign and their actual modular arithmetic. It does not rely on an unproved isomorphism with A₅ or on a supplied multiplication table. The formal generating predicate is closure under identity, the two generators, multiplication and inversion.

Only the universal lower-bound clause is refuted. The submission does not claim to refute an eventual large-q weakening or the separate asymptotic-tightness clause. No exact generation probability is required by the Lean proof.

## Reproduce

Install the official toolchain pinned in `lean-toolchain`, then run:

    lake build
    lake env lean -DwarningAsError=true Counterexample.lean
    python3 check_independent.py
    bash build-pdf.sh

The project imports only Lean's bundled `Std` library; it has no external package dependencies. The PDF build requires a normal LaTeX installation including AMS fonts and hyperref.

## Contents

- `Counterexample.lean`: concrete arithmetic and the formal disproof
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`: reproducible Lean project
- `proof.tex`, `proof.pdf`: full mathematical report and exact subgroup certificate
- `check_independent.py`: independent residue-quotient reconstruction and arithmetic regression checker
- `source.md`: original bilingual conjecture
- `verification/`: clean build logs, axiom output, review, toolchain provenance and eligibility evidence

All changes are confined to this personal submission directory. AI-assisted submission by Galaxy-0, for independent competition review.
