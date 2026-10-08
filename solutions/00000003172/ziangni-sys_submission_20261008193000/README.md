# Conjecture 00000003172: disproof

Actual IHT with one-sparse hard thresholding and step size 1/2, for the nonconstant least-squares objective f(x,y)=x^2/2 and measurement row [1,0], converges linearly from every initial point to an actual sparse global minimizer. Nevertheless every positive restricted strong convexity constant fails on the admissible sparse direction (0,1). This disproves necessity in the source's biconditional.

## Formal scope

Lean constructs the true measurement map and least-squares objective, proves the full Frechet derivative and Euclidean gradient representation, and verifies the actual hard threshold as a nearest one-sparse projection in squared Euclidean distance. It proves actual axis iterations and the full formula for every initial point after its first step. The limit is an actual sparse global minimizer. It proves the exact geometric norm error and full-sequence convergence, and disproves every positive restricted curvature constant. The maximum Banach norm used for convergence equals the Euclidean error here because the error has one nonzero coordinate.

The minimizer may depend on the initial point. This is not uniform recovery of a separately selected ground truth or a uniqueness assertion; neither identifiability nor uniqueness appears in the source. The acceleration-threshold constituent is not required for the disproof.

## Reproduction and validation

Use Lean 4.19.0 and publicly pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. From lean/, run lake update if packages are absent, then lake build. Ignored local .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary computation is needed.

One final full lake build succeeded after draft fixes. Ten final audits use only propext, Classical.choice and Quot.sound; only a redundant tactic-sequencing warning occurs. No incomplete proof, custom axiom, native decision or unsafe code occurs. The two-page PDF compiled without layout warnings, rendered with Poppler and both pages passed visual inspection without clipping or overlap.
