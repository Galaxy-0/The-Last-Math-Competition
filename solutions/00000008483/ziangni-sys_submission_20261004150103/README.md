# Disproof of conjecture 00000008483

The compact singleton family containing [[1,1],[0,1]] has genuine joint spectral radius1: in the reference maximum norm, every length-n product has actual operator norm n+1 and its nth root tends to1. Nevertheless no norm can make this shear nonexpansive, because its powers send e2 to n e1+e2. Therefore it has no extremal or Barabanov norm.

The source omits irreducibility. The report makes the reducible nature of this family explicit and does not contradict Barabanov existence theorems with that additional hypothesis.

The Lean proof uses actual CLMs and operator norms, an explicit matrix/action bridge, complete finite-word product sets, genuine supremum and limsup, and arbitrary positive-definite Mathlib Seminorms. It does not substitute spectral-radius data or an asserted scalar recurrence for the joint spectral radius or norm obstruction.

From lean/, using Lean4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned publicly to c44e0c8ee63ca166450922a373c7409c5d26b00b. Local ignored junctions are not submitted. See report.tex/report.pdf and VERIFICATION.md.
