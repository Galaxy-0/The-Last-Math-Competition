# Zero Brunn–Minkowski deficit does not force congruence

Conjecture 00000007805 has no volume normalization. In dimension one the actual compact convex bodies [0,1] and [0,2] have Minkowski sum [0,3] and Lebesgue volumes 1,2,3, hence zero Brunn–Minkowski deficit. Every pair of isometries leaves their Hausdorff distance at least 1/2. This excludes every vanishing Hausdorff stability modulus, including the stated square-root power. The report explains the necessary nondegeneracy condition for an unspecified monotone transform. Normalized stability and stability modulo homotheties are not refuted.

Lean proves the genuine sets, compactness, convexity, nonempty interiors, Minkowski sum, volumes, deficit, actual Hausdorff distance bound for all isometries, and quantified limit obstructions.

Reproduce in lean/ using Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The successful full build includes six printed theorem axiom audits, using only propext, Classical.choice and Quot.sound. No admitted proofs, custom axioms or native decision procedures.

The complete report is proof.tex/proof.pdf. Existing Tectonic compiled the PDF after the native compiler returned its known platform-directory failure. Both rendered pages were visually checked; a long inline formula was moved to display math to resolve overflow.
