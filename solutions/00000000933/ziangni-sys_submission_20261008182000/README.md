# Conjecture 00000000933: disproof

The nonnormal bounded operators T_k(u,v)=(kv,v) on the complex Banach plane have complete spectrum {0,1} and gap 1. Their two nontrivial Riesz contour projections have actual operator norms at least |k|. The infimum over both nontrivial spectral splittings is therefore unbounded at fixed gap, disproving spectral-separation control without additional hypotheses.

## Formal scope

Lean constructs actual complex continuous linear operators on the Banach product space, proves both explicit resolvent inverse identities and the exact Mathlib spectrum. The Riesz operators are actual complex Bochner circle integrals of this resolvent, normalized by 2 pi i. Cauchy inside-pole and outside-pole calculations give the two complementary projections. Unit-vector testing proves their actual operator norm bounds. Every nonempty proper subset of the spectrum is classified, and the actual real sInf of the resulting two projection norms is proved unbounded.

An empty split would give a zero projection and a vacuous infimum of zero; the report uses the meaningful nontrivial spectral splitting interpretation. Spectral separation alone does not control these nonnormal examples. No resolvent or projection certificate is assumed.

## Reproduction

Use Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, pinned publicly in lakefile and manifest. From lean/, run lake update if packages are absent, then lake build. Ignored local .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary computation is needed.

## Validation

One final full lake build succeeded after draft fixes. All eight final printed axiom audits use exactly propext, Classical.choice and Quot.sound. No incomplete proof, custom axiom, native decision or unsafe code occurs. The two-page PDF compiled with Tectonic without layout warnings, rendered with Poppler and both pages were visually inspected without clipping or overlap.
