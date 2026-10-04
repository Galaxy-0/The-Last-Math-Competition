# Disproof of conjecture 00000001102 (peak of Kazhdan–Lusztig R-polynomials)

The conjecture states that for all `x ≤ w` in a Coxeter group, the Kazhdan–Lusztig
R-polynomial satisfies

```
max R_{x,w} = 2^d · (1 − 2^{−⌈d/2⌉}),   d = ℓ(w) − ℓ(x).
```

The right-hand side equals `2^d − 2^{⌊d/2⌋}`, which is `0, 1, 2, 6` for `d = 0, 1, 2, 3`.
This is false in the symmetric group `S_3` (Coxeter type `A_2`). There, `R_{x,w}` depends only on `d`:

| d | R_{x,w} | example pair |
|---|---------|--------------|
| 0 | `1` | `x = w` |
| 1 | `q − 1` | `e < s₁` |
| 2 | `(q − 1)² = q² − 2q + 1` | `e < s₁s₂` |
| 3 | `q³ − 2q² + 2q − 1` | `e < w₀` |

The statement does not define "max R_{x,w}". The claim fails under every reading
we found, and this already happens for strict pairs `x < w`:

| reading of "max" | values at d = 1, 2, 3 (should be 1, 2, 6) | fails at |
|---|---|---|
| largest coefficient | 1, 1, 2 | d = 2 |
| largest absolute coefficient | 1, 2, 2 | d = 3 |
| sum of absolute coefficients | 2, 4, 6 | d = 1 |
| leading coefficient | 1, 1, 1 | d = 2 |
| degree | 1, 2, 3 | d = 3 |
| number of nonzero terms | 2, 3, 4 | d = 1 |
| value at any fixed `q₀` | `q₀−1`, `(q₀−1)²`, … | d = 1 forces `q₀ = 2`; then d = 2 gives `1 ≠ 2` |
| maximum of `q ↦ R(q)` | `q − 1` is unbounded | d = 1 |

More readings fail as well:
- **The pair `x = w`.** `R_{w,w} = 1` but the formula gives `0`, so every reading with `ρ(1) ≠ 0` fails.
- **Maximum over all pairs with the same `d`.** In `S_3` all pairs with the same `d` share the same R-polynomial, so this reading fails exactly as the per-pair one does.
- **Other normalizations.** The variants `(−1)^d R` and `R̃` also fail (checked in `verify.py`).

The recursion printed in the statement, `R_{x,w} = q R_{xs,w} + R_{x,ws}`, is
garbled. Taken literally, it forces `R ≡ 0` (proved in Lean), which contradicts
`R_{w,w} = 1`. The submission therefore uses the standard R-polynomials. They are
defined by `R_{w,w} = 1`, `R_{x,w} = 0` unless `x ≤ w`, and, for `ws < w`,
`R_{x,w} = R_{xs,ws}` if `xs < x`, and otherwise `(q−1) R_{x,ws} + q R_{xs,ws}`.

## Contents

- `report.tex`, `report.pdf`: the complete mathematical report.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent check that uses only Python 3's standard library. It computes the
  R-polynomials from the Hecke algebra via `T_{w^{-1}}^{-1}` and gets Bruhat order from the tableau
  criterion. It evaluates all readings, including the `(−1)^d R` and `R̃` variants, and also surveys `S_4`.
- `verification.txt`: the fresh build log, the forbidden-token scan and the output of `verify.py`.

## Lean

- **Group and order.** `S3` holds the six permutations as lists. Length is the inversion count `inv`.
  Bruhat order `BruhatLe` is defined inductively as the reflexive-transitive closure of
  `x → x·t` (`t` a transposition, length increasing). `bruhatB_iff` proves that the Boolean
  chain search `bruhatB` decides it on `S_3`.
- **R-polynomials.** `IsRFamily R` is the standard recursive characterization above, required for
  **every** simple `s` with `ws < w`.
  - `R0_isRFamily`: the computed family satisfies it, so the recursion is consistent for every choice of descent.
  - `RFamily_unique`: any two families satisfying it agree.
  - `R_classification`: the table of R-polynomials above.
- **The claim.** `Formula v d` is the conjectured identity multiplied by `2^{⌈d/2⌉}`:
  `v · 2^c = 2^d (2^c − 1)`. `Claim ρ R`, `ClaimStrict ρ R` and `ClaimAgg ρ R` state the
  conjecture for a reading `ρ` (all pairs, strict pairs, maximum over pairs with the same `d`).
  `ClaimMaxValue R` states the "maximum of `q ↦ R(q)`" reading.
- **Main theorem.** `conjecture_00000001102_false R h` proves `¬Claim`, `¬ClaimStrict` and
  `¬ClaimAgg` for every `R` with `IsRFamily R`. This covers the largest coefficient, the largest
  absolute coefficient, the sum of absolute coefficients, the leading coefficient, the degree, the
  number of terms, and the value at every integer `q₀`. It also proves `¬ClaimMaxValue`.
  `conjecture_00000001102_false_R0` instantiates the theorem with the concrete family, which shows
  the hypotheses can be met.
- `not_claim_diag`: the pair `x = w` refutes every reading with `ρ(1) ≠ 0`.
- `literal_recursion_forces_zero` and `literal_recursion_inconsistent`: the literal recursion forces `R ≡ 0`.
- **Not in Lean** (covered in the report and `verify.py`): evaluation at non-integer `q₀`,
  the alternative normalizations, and the facts about general Coxeter groups quoted from the literature.

There is no `sorry`, no `native_decide` and no added axioms. `#print axioms` shows at most
`propext`, `Classical.choice` and `Quot.sound`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想声称：对 Coxeter 群中一切 `x ≤ w`，Kazhdan–Lusztig R-多项式满足
`max R_{x,w} = 2^d (1 − 2^{−⌈d/2⌉})`，其中 `d = ℓ(w) − ℓ(x)`。右端等于 `2^d − 2^{⌊d/2⌋}`，
对 `d = 0,1,2,3` 分别为 `0,1,2,6`。

在对称群 `S_3`（`A_2` 型）中，`R_{x,w}` 只依赖于 `d`：依次为 `1`、`q−1`、`(q−1)²`、`q³−2q²+2q−1`。
题目没有定义"max R_{x,w}"。我们逐一检验了各种合理解读：最大系数、最大绝对值系数、
系数绝对值之和、首项系数、次数、非零项个数、在任意固定点 `q₀` 处的取值、`q ↦ R(q)` 的最大值，
以及"对同一 `d` 的所有区间取最大"。在每种解读下，即使只看严格的 `x < w`，等式也不成立。
此外，`x = w` 时 `R = 1`，而公式给出 `0`。

题目中的递推 `R_{x,w} = qR_{xs,w} + R_{x,ws}` 有误：照字面理解，它迫使 `R ≡ 0`（已在 Lean 中证明），
与 `R_{w,w} = 1` 矛盾。因此我们采用标准的 R-多项式。

Lean 项目从头定义了 `S_3`、长度、Bruhat 序（由反射链生成）以及 R-多项式的递推刻画，
证明了满足该刻画的族存在且唯一，并证明了猜想在上述每种解读下均不成立。
`verify.py` 用 Hecke 代数的独立方法重新计算了全部 R-多项式，并核对了所有数值。
