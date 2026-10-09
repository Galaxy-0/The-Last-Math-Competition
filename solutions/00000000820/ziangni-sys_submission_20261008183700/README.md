# Conjecture 00000000820: disproof

The actual quotient-torus eigenfunction sin(x)sin(y) has eigenvalue2 and a double zero at the origin. Its index(1,1) has gcd1 and eigenvalue2 is not triangular, outside the source's claimed exception. Its first jet vanishes and its nonzero degree-two Taylor polynomial is xy, contradicting order at most1.

## Formal scope

The torus is the actual Real.Angle product, where each Angle is R/(2pi Z). Lean defines the quotient function using Angle.sin, proves continuity on the torus and smoothness of its real periodic lift, and computes actual first and second partial derivatives. The actual Laplacian gives eigenvalue2. The Taylor polynomial through degree two is constructed from these actual derivatives and proved equal to xy, with zero first jet and nonzero mixed derivative. Smooth Taylor expansion therefore gives the first nonzero homogeneous part of degree two; the report states this leading-order link explicitly. Lean verifies the gcd and nontriangular exclusions and proves that this actual zero is not simple.

Only the vanishing-order constituent is refuted; no assertion about the separate zero-set description is needed. No derivative, periodicity or eigenfunction certificate is assumed.

## Reproduction and validation

Use Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b as pinned publicly in lakefile and manifest. From lean/, run lake update if packages are absent and lake build. Ignored .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary computation is needed.

One final full lake build succeeded after draft smoothness fixes, without warnings. All eight final printed axiom audits use exactly propext, Classical.choice and Quot.sound. No incomplete proof, custom axiom, native decision or unsafe code occurs. The final one-page PDF compiled without layout warnings after a real overflow correction, rendered with Poppler and passed visual inspection with no clipping or overlap.
