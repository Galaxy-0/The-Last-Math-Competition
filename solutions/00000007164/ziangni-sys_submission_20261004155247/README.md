# Disproof of conjecture 00000007164

The connected star K₁,₂ and triangle K₃ have the same three vertices but adjacency spectral radii √2 and 2. Hence the star does not maximize spectral radius in the unrestricted graph class stated in the source. The graphs have two and three edges; this does not refute extremality among trees or with a fixed edge count.

The report gives the complete proof. The Lean project constructs actual SimpleGraph objects, their adjacency matrices, full complex spectra via determinant/invertibility, and spectral radii as suprema of spectral moduli.

## Reproduction

Install Lean 4.19.0, enter lean/, and run lake build. Public dependencies are pinned in lakefile.lean and lake-manifest.json, including Mathlib revision c44e0c8ee63ca166450922a373c7409c5d26b00b. No local absolute paths are required.

Files: report.tex, report.pdf, lean/Main.lean and pinned project configuration. See VERIFICATION.md for validation.
