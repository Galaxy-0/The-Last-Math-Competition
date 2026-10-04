# Conjecture 00000000156: disproof

Author: [GodBlf](https://github.com/GodBlf). Submitted October 4, 2026.

For every sign matrix of dimension `n ≥ 3`, subtract row 0 from rows 1 and 2.
Each changed row has even entries. Factoring out 2 from each proves that the
integer determinant is divisible by 4. Its absolute value cannot be prime.
Thus the prime-determinant probability is exactly zero for every `n ≥ 3`, and
cannot be asymptotic to `c/n` for any positive constant `c`.

## Files

- `main.tex`: complete mathematical report.
- `report.pdf`: compiled report.
- `lean/`: pinned Lean 4 / Mathlib project proving the general matrix result,
  the exact probability statement, and the failure of the asymptotic ratio.
- `verification.txt`: build and axiom-audit output.

## Previous submission and correction

[PR #113](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/113)
was merged, then removed in
[commit 4504549](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/commit/450454963d8a4a512a25c3bb9c8654e5c2da40f7).
Its mathematical row-subtraction argument was valid, but its Lean theorems only
established conditional arithmetic and finite examples. They did not connect
arbitrary sign matrices to determinant divisibility or formally refute the
asymptotic claim. The conjecture was consequently restored to unsolved.

This project supplies those missing links. `four_dvd_det` is quantified over
every `n ≥ 3` and every integer sign matrix. `no_prime_det` rules out primality
of the actual determinant's `natAbs`. `primeProbability` counts successful
Boolean matrices in the uniform finite sample space (each Boolean entry encodes
one sign). `probability_zero` proves that event empty in every `n ≥ 3`.
`ratio_tendsto_zero` and `conjecture_false` establish the asymptotic disproof.

## Reproduce

Install the toolchain specified in `lean/lean-toolchain`, then:

```sh
cd lean
lake exe cache get
lake build
lake env lean Check.lean
```

The committed Lake manifest pins all dependencies. `lake update` is only needed
if deliberately regenerating that manifest. The project uses the standard
Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`; no admitted
proofs, additional axioms, or `native_decide` are used. No numerical sampling or
finite enumeration is used in the formal disproof.

To rebuild the PDF, run `pdflatex main.tex` twice. The delivered PDF was built
with pdfTeX and visually checked. The Codex built-in editor's compiler reported
a platform-directory error; the external build succeeded.

## 中文摘要

当 `n ≥ 3`，从第 1、2 行减去第 0 行后，两行所有元素均为偶数。
行列式不变，而从两行分别提出因子 2，得到 `4 ∣ det A`。
因此行列式绝对值不可能是素数，所求概率从三阶起恒为 0，不能渐近于正数 `c/n`。
Lean 验证覆盖任意维度的矩阵、均匀概率定义与渐近公式的否定，补全旧提交被撤回时指出的缺口。
