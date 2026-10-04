# Disproof of conjecture 00000008566

The zero contraction on the complex line is not unitary. In every unitary dilation reproducing its first two powers, the vectors j(1), Uj(1), U²j(1) are orthonormal. Consequently the dilation space has complex dimension at least three, contradicting the asserted dimension two.

The obstruction covers both genuine all-power Sz.-Nagy dilations and the weaker second-order convention. Since the input is one-dimensional, it also excludes interpreting the asserted size as doubling that dimension. It does not assert failure of dilation existence in larger spaces.

The Lean project uses actual continuous linear operators, adjoints, compositions and powers, arbitrary isometric embeddings and unitary equivalences on a complex Hilbert space. It derives actual orthonormality and Module.finrank bounds from the compression equations. No matrix of assumed moments or asserted dimension certificate is substituted.

Reproduce with Lean4.19.0 from lean/:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to public Git revision c44e0c8ee63ca166450922a373c7409c5d26b00b. Ignored local cache junctions are not submitted. See report.tex/report.pdf for the proof and VERIFICATION.md for validation.
