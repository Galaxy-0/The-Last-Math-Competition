# Disproof of conjecture 00000002333

The proposed real Bézout upper bound `(d / sqrt(m))^m * exp(1/2)` fails for the two actual quadratic polynomials `X₀² − 1` and `X₁² − 1` over the reals. Each has total degree 2. The complete solution set consists of four isolated roots, while the proposed bound at `d=m=2` equals `2 exp(1/2) < 4`.

- `proof.tex`, `proof.pdf`: complete mathematical proof and formalization correspondence.
- `lean/Main.lean`: actual multivariate polynomials, total degrees, evaluation, complete solution-set equivalence and cardinality, metric isolation, actual square-root/exponential bound and strict contradiction.
- `lean/lakefile.lean`, `lean/lake-manifest.json`, `lean/lean-toolchain`: reproducible public Git-pinned Lean 4.19.0 / Mathlib project.
- `verification/`: build and direct-source logs, source/eligibility notes, axiom and PDF checks.

## Reproduce

From `lean/`, run:

```text
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. There are no admitted statements, custom axioms, or native decision procedures. Dependency junctions used locally are ignored and are not part of this submission.

The formal isolation theorem proves that any two roots at distance less than 1 in the actual supremum norm are equal. Therefore all counted roots are isolated. The exact classification also excludes any additional solutions.

Both source languages call the displayed expression a solution-count upper bound. This submission refutes that clause; it does not reinterpret the quantity as an expected root count under a random distribution. The two equations have equal degree, positive parameters, and finitely many isolated roots.

The built-in LaTeX compiler was attempted but failed with its existing platform-directory error. Tectonic compiled the delivered PDF; both final pages were rendered and visually inspected.
