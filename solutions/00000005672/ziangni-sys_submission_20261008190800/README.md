# Conjecture 00000005672: disproof

The genuine polynomial family F_mu(x,y)=(mu*x+x^3,mu*y+y^3) has Jacobian mu*I at the fixed origin. At the critical parameter mu=1 the actual complex spectrum is {1}, yet both independent coordinate axes are nonlinearly repelling: arbitrarily small positive starts eventually leave the closed unit neighborhood under true forward iteration. This disproves uniqueness of the critical unstable direction. The valid radius-less-than-one sufficiency is not disputed.

## Formal scope

Lean proves the full Frechet derivative of the family, the fixed point and actual complex matrix spectrum. It constructs the scalar recurrence, proves its lower bound a+n*a^3 for every positive start, and proves eventual escape past every real bound. Both true axis-iterate formulas are verified. The actual repelling-direction property holds for two independent axes; all such directions cannot be contained in a single line. The report distinguishes nonlinear repelling directions from the strictly unstable linearized eigenspace, which has dimension zero here. No certificate of differentiation, iteration, spectrum or instability is assumed.

## Reproduction and validation

Use Lean 4.19.0 and publicly pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. From lean/, run lake update if packages are absent, then lake build. Ignored local .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary numerical computation is needed.

The final full lake build succeeds after draft fixes, with ten final theorem audits using only propext, Classical.choice and Quot.sound. The only warning is a redundant ext-pattern. No incomplete proof, custom axiom, native decision or unsafe code is used. The final one-page PDF compiled without layout warnings, was rendered with Poppler and passed visual inspection without clipping or overlap.
