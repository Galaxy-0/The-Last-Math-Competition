# Conjecture 00000002697: disproof

An actual polynomial map of the affine plane has a two-cycle whose true Jacobians are alternating unipotent shears, each with complete complex spectrum {1}. Every pointwise spectral logarithmic average is zero, but the actual tangent recurrence has Lyapunov exponent log((3+sqrt(5))/2)/2>0 along all iteration counts. This disproves the first constituent under the usual Jacobian-eigenvalue meaning of Jacobi spectrum; no symmetry-group claim is needed.

## Formal scope

Lean constructs the actual polynomial map and proves its full Frechet derivative, verifies the two-cycle recurrence, and computes the complete Mathlib complex spectrum of each true Jacobian matrix. It defines the actual derivative-driven tangent recurrence and proves its even and odd formulas. Actual tangent norms yield logarithmic growth, bounded remainder and the all-n Lyapunov limit, not only a subsequence limit. It proves positivity and zero averages for every pointwise selection from the actual spectra. Zariski tangent spaces of the smooth affine plane are the ordinary two-dimensional tangent spaces, as explained in the report.

No map derivative, orbit, spectral or tangent certificate is assumed. The maximum norm on the plane is an actual Banach norm; finite-dimensional norm equivalence preserves the resulting exponent.

## Reproduction and validation

Use Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, pinned publicly in lakefile and manifest. From lean/, run lake update if packages are absent and lake build. Local ignored .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary computation is needed.

One final full lake build succeeded after draft fixes. All nine final printed audits use exactly propext, Classical.choice and Quot.sound. Only redundant ext-pattern/tactic sequencing linter warnings and a ring tactic suggestion occur. No incomplete proof, custom axiom, native decision or unsafe code occurs. The final two-page PDF compiled without layout warnings, rendered with Poppler and both pages passed visual inspection without clipping or overlap.
