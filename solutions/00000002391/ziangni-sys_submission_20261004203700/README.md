# A two-atom doubling measure has box dimension zero

Conjecture 00000002391's lower bound fails for the genuine measure dirac(-1)+dirac(1). Its support consists exactly of the two atoms. For every support-centered ball of every positive radius, doubling holds with C=2; a radius 3/2 ball about -1 shows that C=2 is the actual smallest global constant.

Actual least finite ball-cover numbers equal 2 at every scale in (0,1]. Their logarithmic covering exponents tend to0, proving both upper and lower box dimension 0, whereas log2/logC=1. Each support point has an actual singleton neighborhood, with covering number 1 and local box dimension 0 as well. The source contains no hypothesis excluding atoms or isolated support points.

Reproduce inside lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Final theorem axiom audits are printed by the full build. The report is proof.tex/proof.pdf; both rendered pages were visually checked. Support and cover numbers are defined through their standard metric/measure conditions, not assigned certificate values.
