# Disproof of conjecture 00000008232

The normalized additive two-player game `v(S)=|S|` on the full Boolean convex geometry has a singleton core `{(1,1)}`, with exactly one genuine extreme point. The claimed vertex count `2^(n−1)` equals 2 for this game. Both payoff and cost core conventions give the same contradiction.

## Contents

- `proof.tex` and `proof.pdf`: complete proof and honest source-convention discussion.
- `lean/Main.lean`: actual finite convex geometry, feasible coalitions, modular game and both game inequalities, full coalition core definitions, exact singleton cores, Mathlib extreme-point sets and actual vertex-count failure.
- `lean/`: public Git-pinned Lean 4.19.0 / Mathlib project configuration.
- `verification/`: full source/eligibility evidence, compile logs, axiom audits and PDF QA.

## Reproduce

From `lean/`, run:

```text
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

No admitted statements, custom axioms or native decision procedures are used. The axiom audits use only standard logical axioms. Local ignored dependency junctions and build products are not part of the submission.

The unusual phrase “anti-convex games” is not separately defined in either source language. The game satisfies both standard non-strict supermodular and submodular inequalities, with equality. Its full Boolean feasible family is an actual finite convex geometry. There is no strict nonmodularity hypothesis in the source. The report explains this correspondence and computes both entire core conventions, rather than imposing an unspecified restricted game class.

This refutes the vertex-count conjunct; the other conjuncts need not be resolved. A singleton core is a genuine zero-dimensional polytope with one vertex.

The built-in LaTeX compiler was attempted but failed with its existing platform-directory error. Tectonic compiled the delivered PDF, and both final pages were rendered and visually inspected.
