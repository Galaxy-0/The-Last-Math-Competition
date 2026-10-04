# Disproof of conjecture 00000000377

A parabolic periodic multiplier is a root of unity. A real Liouville number cannot be a root of unity: the only real roots of unity are ±1, both rational. Thus the actual parameter set on the Mandelbrot boundary described in the first dimension clause is empty and has Hausdorff dimension 0, not 1.

Lean defines the actual quadratic polynomial z²+c and composition iterates, proves evaluation agrees with actual function iteration, and defines the multiplier as the actual complex derivative. A proved bridge identifies it with polynomial-derivative evaluation. The Mandelbrot set is the actual bounded-critical-orbit set and its frontier is used in the parameter definition. Actual periodicity, the finite-order parabolic multiplier condition and Mathlib's genuine Liouville predicate are imposed. Emptiness holds even before an additional Julia-set restriction, hence also after that restriction. Actual dimH is 0 and unequal to 1. The badly-approximable clause is not addressed.

Reproduce from lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Local ignored junctions only reuse existing caches. Final full build succeeds with six standard-only axiom audits. No admitted proofs, custom axioms or native decision procedures.

Tectonic compiled the final two-page PDF, and both pages were rendered and inspected after correcting an overfull line. The second page contains the primary-source reference. Built-in editor/compiler was attempted; its known platform-directory failure was recorded. Milnor's original paper states the root-of-unity definition on page 2: https://www.math.stonybrook.edu/files/dynamics/orm.pdf .