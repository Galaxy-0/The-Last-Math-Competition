# Counterexample to conjecture 00000000603

The conjecture says that for every torus knot `T(p,q)` the coefficient
sequence of the Conway polynomial `∇(z)` peaks at position
`⌊(p−1)(q−1)/4⌋`. This peak-position clause is false.

For `T(2,25)` the predicted position is `⌊1·24/4⌋ = 6`, but

```
∇_{T(2,25)}(z) = 1 + 78z² + 1001z⁴ + 5005z⁶ + 12870z⁸ + 19448z¹⁰ + 18564z¹²
               + 11628z¹⁴ + 4845z¹⁶ + 1330z¹⁸ + 231z²⁰ + 23z²² + z²⁴.
```

The largest coefficient is `19448` at `z¹⁰`, which is index 5 in the
sequence of even coefficients. Both readings of "position 6" (the coefficient
of `z¹²`, `18564`, and the coefficient of `z⁶`, `5005`) are strictly smaller.
For `T(2,61)` the predicted position `15` fails under every indexing
convention (power of `z`, even-coefficient index from 0, or from 1). The
unique peak there is `[z²⁶] = C(43,26) = 421171648758`.

The Conway polynomial of `T(2,n)`, the closure of the braid `σ₁ⁿ`, is
determined by the skein relation `∇(L₊) − ∇(L₋) = z∇(L₀)` applied to one
crossing: `F₀ = 0` (2-component unlink), `F₁ = 1` (unknot), and
`F_{n+2} = F_n + z F_{n+1}`. For `n = 2k+1` this gives
`[z^{2i}] = C(k+i, 2i)`.

## Contents

- `report.tex`, `report.pdf`: the complete mathematical report.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent check using only Python 3's standard library. It runs the
  skein recursion, derives the Conway polynomial from the Alexander polynomial
  `(t^{pq}−1)(t−1)/((t^p−1)(t^q−1))` and compares with the closed form,
  and surveys all `T(p,q)` with `p < q ≤ 30`.
- `verification.txt`: the build log, axiom audit and Python output.

## Lean

`ConwaySkein c` states the three skein facts above for a family of
polynomials in `z`, given as coefficient functions. `skein_unique` proves
that these facts determine every coefficient. `ref_skein` proves that they
are consistent. `ref_25` and `ref_61_unique_peak` compute the coefficients with
`decide`. `alexander_25` and `alexander_61` cross-check the skein coefficients
against the classical Alexander polynomial `Δ_{T(2,n)}(t) = Σ_{j<n} (−t)^j`
through the identity `∇(s − s⁻¹) = s^{−(n−1)} Δ(s²)`. `alexander_61` uses
`decide +kernel`, which is checked by the kernel and is not `native_decide`.
`conjecture_00000000603_false` proves that the peak clause `PeakClaim` fails for all `T(2,n)` under all three readings.

The project has no `sorry`, no `native_decide`, and no added axioms.
`#print axioms` shows only `propext` and `Quot.sound`. `ref_25`,
`alexander_25` and `alexander_61` use no axioms at all.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想声称环面纽结 `T(p,q)` 的 Conway 多项式系数序列的峰位于 `⌊(p−1)(q−1)/4⌋`。
这一条不成立。`T(2,n)`（`σ₁ⁿ` 的闭包）的 Conway 多项式由 skein 关系唯一确定：
`F₀=0`、`F₁=1`、`F_{n+2}=F_n+zF_{n+1}`。
对 `T(2,25)`，偶次系数为 `1, 78, 1001, 5005, 12870, 19448, 18564, …`，
峰在下标 5（`z¹⁰`），而公式给出 6。
对 `T(2,61)`，无论按哪种下标约定，预测位置 15 都不是峰（唯一峰在 `z²⁶`）。
猜想是多个子句的合取，只要其中一个子句为假，整个猜想即被否定。
Lean 项目从 skein 关系出发计算系数，并证明峰位置子句的否定。
Python 脚本通过 Alexander 多项式另行独立验证。
