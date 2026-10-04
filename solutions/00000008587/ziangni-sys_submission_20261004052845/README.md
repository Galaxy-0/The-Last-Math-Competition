# Disproof of conjecture 00000008587

The actual scalar operator algebra `{a I : a∈ℂ}` acting faithfully and unitally on `ℂ³` has a triangularizing standard basis, but every vector-space basis of this representation has cardinality 3. Its minimum triangularizing-basis size is therefore 3, contradicting the source's explicit upper bound 2.

## Contents

- `proof.tex`, `proof.pdf`: complete proof and fixed-representation interpretation.
- `lean/Main.lean`: genuine scalar algebra homomorphism, range subalgebra, faithfulness, unit, continuity, commutativity, actual matrices and triangularization, arbitrary-basis finiteness and cardinality, and final contradiction.
- `lean/`: public Git-pinned Lean 4.19.0 / Mathlib project configuration.
- `verification/`: full original source, strengthened eligibility, compile logs, axiom audit and PDF QA.

## Reproduce

From `lean/`, run:

```text
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

No admitted statements, custom axioms or native decision procedures are used. No auxiliary computations are needed. Only standard logical axioms occur in the printed dependency audits. Ignored local cache junctions and build products are not committed.

The bases are genuine vector-space bases making the representation matrices upper triangular, as defined in the source. The example fixes the actual operator algebra acting on its given representation space; it does not replace a representation basis by an abstract algebra basis or minimize over different representation spaces. All bases, not just the standard basis, are covered. The source's dimension-bound conjunct is refuted; other conjuncts need not be resolved.

The built-in saved-source editor/compiler was attempted but encountered its existing platform-directory error. Tectonic compiled the delivered PDF, and both final pages were rendered and visually inspected.
