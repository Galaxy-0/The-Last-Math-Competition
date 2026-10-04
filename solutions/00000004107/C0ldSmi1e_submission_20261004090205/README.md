# Disproof of conjecture 00000004107

A coordinate plane and its transverse coordinate axis in real three-dimensional space give a counterexample to strict coefficient alternation:

```text
U = {(a,b,0) : a,b ∈ ℝ}
W = {(0,0,c) : c ∈ ℝ}
χ_{U,W}(t) = t³ − t² − t + 1.
```

The coefficients of `t²` and `t` are both `−1`. All four coefficients are nonzero, so ignoring zero coefficients or reversing coefficient order cannot restore alternation.

The exact [English and Chinese conjecture](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/0862407ef50dda4f7376342ca3e79368dce942d2/conjectures/00000004107.md) is copied in `conjecture.md`. Both versions concern **subspace arrangements**; neither restricts members to hyperplanes or to equal dimensions. The example has distinct, proper, nonzero, incomparable members. The universal sign-alternation clause is false, so the additional dimension-spectrum assertion is not needed for the disproof.

## Actual geometric invariant

The intersection poset contains the ambient space, the plane, the axis and the zero subspace, ordered by reverse inclusion. Their actual dimensions are `3,2,1,0`, and the Möbius values from the ambient element are `1,−1,−1,1`. The defining sum therefore gives the displayed polynomial.

The standard definition is documented in Björner–Ekedahl, [*Subspace Arrangements over Finite Fields: Cohomological and Enumerative Aspects*](https://arxiv.org/abs/math/9612217), §2 and §3, equation (3.1). The definitions apply over a general field; our example is over the reals.

All Lean declarations use namespace `Conjecture4107`; files are under `lean/`.

| File | Role |
|---|---|
| `Conjecture4107/Geometry.lean` | Actual real submodules, explicit linear equivalences and dimensions, intersection and noncontainment facts |
| `Conjecture4107/Arrangement.lean` | Generic intersection poset of actual finite intersections, reverse inclusion, standard Möbius characteristic sum, complete concrete poset computation |
| `Conjecture4107/Signs.lean` | Strict and weak coefficient sign predicates and the obstruction from consecutive negative coefficients |
| `Conjecture4107.lean` | Actual polynomial coefficients and final universal sign-claim negation |
| `Check.lean` | Definition printouts and theorem type/axiom audits |

The poset elements are submodules obtained from actual intersections, not labels in an unrelated four-element model. Equal intersections are identified. The empty subfamily gives the actual ambient space. The polynomial uses Mathlib's `IncidenceAlgebra.mu` and actual `Module.finrank` values. No assumed correspondence or surrogate polynomial replaces the invariant.

## Reproduction

Lean **4.19.0** and Mathlib **v4.19.0** are pinned. Mathlib's exact revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`; the manifest pins all dependency revisions. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture4107/Geometry.lean
lake env lean -DwarningAsError=true Conjecture4107/Arrangement.lean
lake env lean -DwarningAsError=true Conjecture4107/Signs.lean
lake env lean -DwarningAsError=true Conjecture4107.lean
lake env lean -DwarningAsError=true Check.lean
```

The optional cache supplies compiled dependencies; the submission must still be built. If the cache executable is unavailable, use `lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`.

Run `tectonic main.tex` to reproduce the report. The package includes the full proof, matching PDF, independent internal semantic review, verification logs, eligibility evidence and file hashes. No numerical auxiliary program is needed. Local verification and internal review are separate from official maintainer acceptance.
