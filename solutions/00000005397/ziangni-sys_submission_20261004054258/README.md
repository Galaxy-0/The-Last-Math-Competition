# Disproof of conjecture 00000005397 for a fixed torus translation

Consider the actual torus (R/Z)^2 and the fixed translation with real frequency vector (sqrt(2),1). These two components are Q-linearly independent, but the second circle increment is zero. Every integer orbit, from any initial point, lies in a proper closed coordinate fiber and is not dense. The actual forward iterates are not dense either.

The source does not explicitly distinguish discrete and continuous time. This submission uses the standard iteration-of-one-fixed-translation convention and explicitly makes that scope clear. It does not refute the rational-independence criterion for continuous-time linear flows. Independent semantic review should assess this convention against the original.

The full argument is in report.tex and the visually checked two-page report.pdf. lean/Main.lean uses actual AddCircle, LinearIndependent over Q, translation and inverse, integer orbits, map iterates, closed sets and Dense.

## Reproduction

Use Lean 4.19.0. From lean/, run:

```text
lake update
lake exe cache get
lake build
lake env lean Main.lean -DwarningAsError=true
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. All public dependencies are pinned Git revisions; local .lake junctions and caches are ignored. Compile the report with Tectonic or a standard LaTeX engine. No auxiliary computation is needed.
