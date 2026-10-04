# Disproof of conjecture 00000000420

The exact proposed angular density on `[-π/2, π/2]` integrates to `8*sqrt(2)/(3*π) > 1`. Its associated Lebesgue-density measure is not a probability measure. Lean also proves that no sequence of probability measures can converge weakly to it.

This rules out a necessary component of the claimed tableau-angle limit for every possible probability-law sequence. No particular tableau model or finite numerical sample is substituted for the stated claim. The submission does not identify the actual limiting law or establish a renormalized replacement.

## Contents

- `main.tex` and `main.pdf`: complete mathematical report and matching three-page PDF.
- `conjecture.md`: unchanged original bilingual statement.
- `lean/`: full Lean project, pinned dependencies, and axiom audit.
- `SEMANTIC_REVIEW.md`: internal source review, distinct from official maintainer review.
- `verification/`: build output, audit output, document log, eligibility record, and file hashes.

## Reproduce the proof

Install Lean 4.19.0 using `lean/lean-toolchain`, enter `lean/`, and run:

```sh
lake exe cache get
lake build
for source in Definitions.lean DensityBounds.lean DensityIntegral.lean Probability.lean Conjecture420.lean Check.lean
do
  lake env lean -DwarningAsError=true "$source" || exit 1
done
```

The cache is optional; `lake build` can compile the dependencies from source. If a platform cannot load the native cache executable, the equivalent source-run command is:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
lake build
```

Preserve the committed manifest to reproduce its dependency revisions. Mathlib is pinned to v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all nine dependency revisions were checked against the manifest.

`Check.lean` prints the density, interval, actual measure, finite-measure wrapper, and concluding theorem type. It audits twelve central results; all depend only on `propext`, `Classical.choice`, and `Quot.sound`. No auxiliary numerical computation is needed: the exact integral and all measure-theoretic consequences are formally proved.

## Source map

| Module | Mathematical role |
|---|---|
| `Definitions` | Exact density, support, and restricted-Lebesgue `withDensity` measure. |
| `DensityIntegral` | Continuity, integrability, and exact integral by substitution. |
| `DensityBounds` | Nonnegativity on the support and exact mass greater than one. |
| `Probability` | Density-to-mass identity, non-normalization, and impossibility as a weak probability limit. |
| `Conjecture420` | Final `conjecture420_disproof`, covering every probability-measure sequence. |

## Reproduce the report

Compile `main.tex` with a standard LaTeX distribution, for example `latexmk -pdf main.tex` or `tectonic main.tex`. The checked-in PDF was exported with Tectonic 0.17.0 from this exact source, which also passed the desktop LaTeX compiler. All three pages were rendered and visually inspected.

The entire contribution is confined to this personal submission folder. All verification records describe local checks; acceptance remains the competition maintainers' decision.
