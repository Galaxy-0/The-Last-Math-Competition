# Conjecture 00000001236: FALSE

**English (verbatim from the filed conjecture).** "Definition: The minimal total weight of recurrent configurations is the minimum chip count among stable and recurrent configurations. Conjecture: This minimum equals the max-stable weight minus the explicit row-minimal sum of a matrix M, where M is the rounding of the inverse of the (V−1)×(V−1) reduced Laplacian; the minimal configuration is unique up to isomorphism."

**中文(原文逐字).** "定义:recurrent 构形的极小总重量指稳定且循环的构形中芯片总数的最小值。猜想:该极小值等于 max-stable 构形重量减去显式矩阵 M 的行最小和,M 为 (V−1)×(V−1) 的简约 Laplacian 逆的取整;极小构形在同构意义下唯一。"

**Verdict.** FALSE. On the path 1–2–3 with the sink attached to vertex 3, the
reduced Laplacian has determinant 1 and its inverse is the integer matrix
M = [[3,2,1],[2,2,1],[1,1,1]] — so every rounding convention coincides. The
"row-minimal sum" of M is 3 under *both* possible readings (sum of the row
minima 1+1+1 = 3, and minimum row sum min{6,5,3} = 3). The max-stable weight
is 0+1+1 = 2, so the conjecture predicts 2 − 3 = −1. But det L = 1 makes the
sandpile group trivial, so there is exactly one recurrent configuration,
(0,1,1), of weight 2. 2 ≠ −1; the predicted value is even negative, while all
weights are nonnegative. (The uniqueness clause, by contrast, does hold here —
the failure is in the value identity.)

## Reproduce

```sh
python3 reproduce.py        # exact recomputation (Fraction arithmetic),
                            # burning-test and forbidden-subconfiguration
                            # cross-checked, on P2+sink, P3+sink, P4+sink
cd lean4
lake build
lake env lean Check.lean
```

## Verification status

`lake build` and `lake env lean Check.lean` pass with the pinned core-Lean
toolchain `v4.33.1` (no Mathlib). `Check.lean` prints `#print axioms` for every
theorem; all are axiom-free (no `sorryAx`, no `Classical.choice`, not even
`propext`). The Lean file formalises: L·M = I (so M is the exact, hence
rounded, inverse), det L = 1, both readings of the row-minimal sum (= 3), the
Dhar burning-test characterisation of recurrence on this graph, uniqueness of
the recurrent configuration (0,1,1), the minimum recurrent weight 2, and the
resulting failure of the conjectured identity under either reading.

## Files

- `main.tex` / `main.pdf`: full write-up of the counterexample.
- `lean4/`: pinned core-Lean project, zero axioms, zero `sorry`.
- `reproduce.py`: independent exact-arithmetic checks.
