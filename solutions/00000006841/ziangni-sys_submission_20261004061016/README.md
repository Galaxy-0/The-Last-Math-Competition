# Proof of conjecture 00000006841

Orthogonal subspace reflections and arbitrary finite compositions are surjective linear isometries preserving inner products. The full real/complex Hilbert-space theorem applies to every closed subspace; a more general theorem covers any subspace admitting orthogonal projection.

The standard operation is reflection 2P−I and “combination” means composition. Nonclosed subspaces are included whenever orthogonal projection exists; no projection is assumed to exist for every nonclosed subspace. Compositions need not themselves be involutions.

See report.tex and report.pdf for the full proof and scope. The actual Mathlib reflections, projections, maps, arbitrary lists, metric isometry and inner-product preservation are encoded in lean/Main.lean.

From lean/, run:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned. A standard Internet-enabled Lake installation fetches the public dependencies. Local ignored junctions used for validation are not part of the submission.
