# Disproof of conjecture 00000000308

The real number `sqrt(2)`, embedded in the complex plane, satisfies

`1 / (4 * |q|^2) ≤ |sqrt(2) - p/q|`

for every Gaussian-integer numerator `p` and every nonzero Gaussian-integer denominator `q`. Thus it belongs to the standard complex badly approximable set and to the real axis, refuting the universal empty-intersection clause.

## Definition and scope

The conjecture describes bad approximation informally. This submission explicitly uses the standard Gaussian-rational definition: there is a positive constant `c` such that `|z-p/q| ≥ c/|q|^2` for all `p,q ∈ Z[i]`, `q ≠ 0`. See [Esdahl-Schou–Kristensen, equation (2)](https://doi.org/10.1017/S0017089510000042) and [Hines, introduction, page 1](https://arxiv.org/pdf/1707.07231v3). These references establish terminology only; the proof does not assume their substantive theorems.

Division and absolute values are in the complex numbers. All numerator/denominator pairs are covered, without a coprimality condition or size cutoff. The line is the actual nondegenerate real axis. The final theorem negates the first conjunct; no separate result about the measure or rate clauses is asserted.

## Contents

- `main.tex` and `main.pdf`: complete report and matching three-page PDF.
- `conjecture.md`: unchanged original bilingual statement.
- `lean/`: complete formal proof project, pinned dependencies, and audit.
- `SEMANTIC_REVIEW.md`: internal source review, separate from official review.
- `verification/`: build and axiom output, document log, eligibility record, and file hashes.

## Reproduce the proof

Install the toolchain in `lean/lean-toolchain` (Lean 4.19.0), enter `lean/`, and run:

```sh
lake exe cache get
lake build
for source in Definitions.lean RealBound.lean ComplexBound.lean Conjecture308.lean Check.lean
do
  lake env lean -DwarningAsError=true "$source" || exit 1
done
```

The cache is optional; `lake build` can compile dependencies from source. If the native cache executable fails to load on a platform, use:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
lake build
```

Preserve the committed manifest to reproduce its revisions. Mathlib is pinned to v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all nine dependency revisions were checked.

`Check.lean` displays the actual approximation set, line definition, universal claim, Gaussian inequality, and concluding theorem. Eight central theorem audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Source map

| Module | Role |
|---|---|
| `Definitions` | Standard complex bad approximation with actual Gaussian integers, complex division, and real affine lines. |
| `RealBound` | Uniform integer inequality `1/4 ≤ |m|*|m*sqrt(2)-n|` for every nonzero integer `m` and integer `n`. |
| `ComplexBound` | Transfer using a nonzero denominator coordinate; bound for every Gaussian rational and membership in `BadC`. |
| `Conjecture308` | Explicit real-axis witness and negation of the universal empty-intersection claim. |

## Reproduce the report

Compile `main.tex` with `latexmk -pdf main.tex` or `tectonic main.tex`. The checked-in PDF was exported with Tectonic 0.17.0 from this exact source, which also passed the desktop LaTeX compiler. All three pages were rendered and visually inspected.

No auxiliary numerical computation is used or required. The contribution changes only this personal submission folder. These records document local verification; acceptance remains the maintainers' decision.
