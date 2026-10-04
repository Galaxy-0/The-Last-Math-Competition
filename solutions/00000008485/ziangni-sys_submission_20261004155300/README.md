# Disproof of conjecture 00000008485

On the actual compact discrete two-point dynamical space with identity map, the continuous observables f=(1,0) and g=(0,1) have integration image exactly {(1,0),(0,1)} over ergodic invariant probability measures. These are both Pareto points, but their midpoint is absent, so the actual frontier is not convex.

Lean proves both Diracs are genuinely ergodic, classifies every ergodic probability measure as one of these actual measures, computes the actual Bochner integrals, and identifies the complete integration image and its quantified northeast Pareto frontier. It then disproves Mathlib's actual Convex predicate. The reference system with Dirac 0 is genuinely ergodic. Neither source imposes full support. The source explicitly varies over ergodic measures; all invariant measures or their convex hull would instead give the segment.

Reproduce from lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Ignored local junctions only reuse the shared cache. Full build prints six axiom audits. No admitted proofs, custom axioms or native decision procedures.

The complete proof and correspondence are in disproof.tex/disproof.pdf. Built-in editor/compiler was attempted with its known platform-directory failure; Tectonic compiled the final two-page PDF and both pages were rendered and visually inspected. Only the first convexity clause is refuted.