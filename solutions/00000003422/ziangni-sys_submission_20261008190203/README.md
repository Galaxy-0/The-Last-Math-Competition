# Counterexample to 00000003422

The positive lazy reversible chain P = [[3/4,1/4],[1/4,3/4]] has stationary distribution (1/2,1/2). Its canonical fundamental matrix Z = (I - P + Pi)^(-1) is [[3/2,-1/2],[-1/2,3/2]]. Complete complex spectra are {1,1/2} and {1,2}. This refutes both the arithmetic-complement and literal set-complement readings of the source's spectral assertion.

The report explains the correct reciprocal-gap map on nonstationary modes and also checks the deviation-matrix convention. No hitting-time formula is required. The standard fundamental-matrix definition is sourced in the report, and all example computations are proved directly.

Run `lake build` in `lean/` with Lean 4.19.0 and the pinned public dependencies. See `report.pdf` and `report.tex` for the complete proof and scope discussion.
