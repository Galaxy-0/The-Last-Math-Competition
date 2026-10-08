# Disproof of 00000000010

The square-free integer polynomial f = X has discriminant 1 and
Bateman-Horn constant 1. Each prime contributes exactly one root and
local factor 1, so the actual prime partial products converge to 1.
The asserted upper bound C_f <= 2 log D_f becomes 1 <= 0.
The stated scope has no degree or discriminant restriction.

Includes `proof.tex`, compiled `proof.pdf`, and the project `lean/`.
Use Lean 4.19.0, pinned by `lean-toolchain`. In `lean/`, run `lake update`
if dependencies are absent, then `lake build`. The lakefile and manifest
pin public Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
Local validation used ignored junctions to this exact cache.
Compile the document using `tectonic proof.tex`.

One full final lake build passed on 2026-10-08 after a draft repair.
Printed audits for square-freeness, actual root factorization,
discriminant, finite-field roots, prime product limit and final false
upper bound contain only propext, Classical.choice and Quot.sound.
No sorry, admit, native_decide, custom axioms or unsafe declarations.
The final two-page PDF compiled; both rendered pages were visually
inspected once and have no clipping, overlap or missing glyphs.

The discriminant is computed using the standard leading-coefficient
and root-difference product with verified factorization of X.
The constant is defined as the limit of the actual prime partial
products, not stipulated. The disproof targets only the upper bound;
it makes no use of the separate lower bound's division by log 1.
