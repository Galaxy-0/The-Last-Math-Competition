# Conjecture 00000003556: finite diameter partitions fail in infinite dimension

In the actual real Hilbert space `l²(N)`, let `S` be the set of coordinate unit vectors. Distinct vectors have distance `sqrt(2)`, so `diam(S) = sqrt(2)`. Every part of strictly smaller diameter contains at most one vector. Thus no finite cover, and hence no finite partition, into parts of smaller diameter exists.

This refutes the source's finiteness clause under the standard Borsuk interpretation for nonempty bounded sets of positive diameter. It remains a counterexample if the ambient spaces are restricted to Hilbert spaces. Both language versions of the source lack a compactness hypothesis. The separate, unspecified hyperplane-obstruction claim is not formalized or needed. Compact-set variants are outside the conclusion.

## Contents

- `main.tex`, `main.pdf`: complete proof, scope, and correspondence with Lean.
- `SOURCE.md`: byte-for-byte original bilingual source.
- `lean/Main.lean`: actual Hilbert space, coordinate vectors, infinite dimension, distances, boundedness, exact metric diameter, and finite-cover obstruction.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`: portable pinned Lean project.
- `verification/BUILD.json` and adjacent logs: actual build, axiom, hash, and PDF evidence.
- `verification/SELF_REVIEW.md`: authoring-agent adversarial review.

## Reproduce

With Lean installed through elan, run from `lean/`:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

Lean is pinned to version 4.19.0 and Mathlib to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Transitive dependencies are locked in the manifest, with public Git URLs and no local dependency paths. An optional `lake exe cache get` can obtain Mathlib's official dependency artifacts on a fresh machine.

From the submission directory, build the PDF with:

```text
tectonic main.tex
```

No auxiliary numerical program is necessary: this is an infinite exact argument, fully represented by the Lean counterexample.

## Verification and interpretation

The fresh-build evidence records actual commands and exit codes. Only unmodified, commit-pinned official dependency artifacts may be reused; the submission's own Lean output is generated in a fresh directory. The source contains no `sorry`, `admit`, custom axiom, opaque assertion, or `native_decide`. The final theorem's printed axiom dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`.

Mathlib's `lp` space is the genuine analytic ambient space. Its inner product and completeness instances are supplied by the pinned library. Linear independence and the negation of finite dimensionality are proved in this project. `Metric.diam` is applied only to bounded sets: every cover part lies inside the bounded witness. The cover predicate does not require disjointness, so its impossibility is stronger than impossibility of a partition. Allowing arbitrary cover subsets of the ambient space does not help, since intersecting each with `S` preserves coverage and cannot increase its diameter.

The infinite-color diameter-graph interpretation, its exact countable cardinality, and the noncompactness explanation are established in the paper but not asserted as separately formalized Lean theorems. The formalized universal clause is exactly the finite-cover assertion for all nonempty bounded positive-diameter subsets of this particular infinite-dimensional Hilbert space.

The native source editor was requested and compilation was attempted. The compiler reported `Unable to find standard directories for platform`; the existing Tectonic installation therefore exported the actual PDF. That failure and the successful export are recorded separately. The final two-page PDF compiled without warnings, and both rendered pages were visually inspected successfully.

Authorship and review: the authoring agent performs a self-review. A parent agent must separately review the source, proof, evidence, and PDF before publication. No GitHub writes are performed by this agent.
