# Conjecture 00000001616: disproof

The explicitly asserted Eisenstein norm form is false: the actual norm of 1+omega is 1, while Q(1,1)=2. The complex primitive cube root omega=(-1+i sqrt(3))/2 gives the Eisenstein embedding a+b omega and norm a²−ab+b² for every integer pair. This disproves that explicit constituent of both source versions; no separate billiard gap-distribution assertion is made.

## Formal scope

Lean uses an actual Complex number omega, proves its quadratic identity and primitive cube-root property, embeds integer coefficient pairs into Complex, and computes Mathlib Complex.normSq for every pair. The witness contradicts the universally asserted a²+b² formula. The Gaussian basis 1,i has the latter norm form; changing rings would change the statement.

## Reproduction

Use Lean4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, pinned publicly in lakefile and manifest. From lean/, run lake update if packages are absent and lake build. Local ignored .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary computation is needed.

## Validation

One final full lake build succeeded after draft fixes, without warnings. All five printed final theorem axiom audits use exactly propext, Classical.choice, Quot.sound. No admissions, custom axioms, native decision or unsafe code occurs. The one-page PDF compiled with Tectonic without layout warnings, rendered with Poppler and was visually inspected with no clipping or overlap.
