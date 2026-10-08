# Conjecture 00000002515: proof

For every actual real continuous multilinear map on a finite family of nontrivial finite-dimensional normed spaces, its operator norm is attained on a tuple of unit vectors. The actual gain there equals the norm and bounds every other unit-tuple gain. This includes all ordinary finite real tensor contractions on positive-dimensional Euclidean factors, the zero tensor, and every finite arity, including zero arity.

## Formal scope

Lean uses the actual Mathlib ContinuousMultilinearMap operator norm, defined as the infimum of global product-norm bounds. Compactness and nonemptiness of the unit-tuple set produce a genuine maximizer of the continuous gain. Actual multilinear normalization extends its bound to all tuples, with zero coordinates handled directly by multilinearity. The least-bound norm property proves equality; no maximizing certificate is assumed. Nontrivial factors explicitly provide unit vectors, as required by the conventional unit-vector extremal formulation.

## Reproduction and validation

Use Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, pinned publicly in lakefile and manifest. From lean/, run lake update if packages are absent, then lake build. Ignored local .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary computation is needed.

One final full lake build succeeded after draft fixes. All six final printed axiom audits use exactly propext, Classical.choice and Quot.sound. Only unused section-variable linter warnings occur. No incomplete proof, custom axiom, native decision or unsafe code occurs. The final one-page PDF compiled without layout warnings, rendered with Poppler and passed visual inspection without clipping or overlap.
