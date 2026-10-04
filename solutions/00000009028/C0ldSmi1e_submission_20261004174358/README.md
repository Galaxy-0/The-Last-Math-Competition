# Disproof of conjecture 00000009028

Determinant parity does not characterize evenness of an integral Euclidean lattice. The actual A2 lattice is even with Gram determinant 3. A second actual rank-two lattice has Gram determinant 2 but contains a vector of squared length 1. Both implications therefore fail.

The formalized assertion is the explicit lattice-evenness criterion in the exact bilingual source, included as `conjecture.md`. The report explains the Gram-determinant convention and the relation to the conjecture's theta context. It does not invent a modular group, level, character formula, or formal theta-series theorem.

## Reproduce the Lean verification

The project pins Lean 4.19.0 and Mathlib v4.19.0, with all dependency revisions locked in the manifest. From `lean/`, after installing the pinned toolchain and fetching the pinned dependencies:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture9028/Definitions.lean
lake env lean -DwarningAsError=true Conjecture9028/A2.lean
lake env lean -DwarningAsError=true Conjecture9028/Diagonal.lean
lake env lean -DwarningAsError=true Conjecture9028.lean
lake env lean -DwarningAsError=true Check.lean
```

`Check.lean` prints 28 definitions and named instances, and checks the types and transitive axiom dependencies of all 47 named theorem/instance declarations: 43 theorems and four instances. Only the usual `propext`, `Classical.choice`, and `Quot.sound` are permitted. There are no admitted proofs, custom axioms, native decision proofs, or auxiliary numerical computations.

## Contents

- `lean/Conjecture9028/Definitions.lean`: integer parity, actual pairing integrality, evenness, actual Gram determinant, and universal necessity/sufficiency/characterization statements.
- `lean/Conjecture9028/A2.lean`: the sum-zero Euclidean plane; real and integer bases; discrete full lattice; rank, positivity, integrality and evenness; Gram determinant 3.
- `lean/Conjecture9028/Diagonal.lean`: the plane y=z; real and integer bases; discrete full rank-two integral lattice; Gram determinant 2; squared-length-1 lattice witness.
- `lean/Conjecture9028.lean`: `determinant_not_necessary`, `determinant_not_sufficient`, `both_directions_fail`, and `conjecture_false`.
- `main.tex` and `main.pdf`: matching mathematical report. Standard LaTeX packages only; compile with `pdflatex main.tex` twice or `tectonic main.tex`.
- `VERIFICATION.md`, `SEMANTIC_REVIEW.md`, and `verification/`: exact execution, identity, eligibility, and independent internal review records.

The verification records document the commands actually run, including a fresh project build in an independent directory with pinned dependency caches reused. Local validation and internal review are distinct from official maintainer acceptance.
