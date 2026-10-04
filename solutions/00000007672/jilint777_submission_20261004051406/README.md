# Counterexample to conjecture 00000007672

The conjecture says that for the q-Fibonacci polynomials
`F_n(q) = Σ_j [n−1−j choose j]_q q^{j²}`, the gcd `gcd(F_n, F_m)` in `ℤ[q]`
equals `F_{gcd(n,m)}` times a correction factor. This is false for
`(n, m) = (6, 3)`:

```
F_3 = 1 + q
F_6 = 1 + q + q² + q³ + 2q⁴ + q⁵ + q⁶ = F_3 · (−1 + 2q − q² + 2q³ + q⁵) + 2
```

`F_3(−1) = 0` but `F_6(−1) = 2`, so every common divisor of `F_6` and `F_3` in
`ℤ[q]` is `±1`, and `gcd(F_6, F_3) = 1`. Since `gcd(6,3) = 3`, the claim would
make `1` a multiple of `F_3 = 1 + q`. That is impossible: evaluate at
`q = −1`. Allowing the correction factor to have rational coefficients does
not help.

The same argument refutes the claim for every pair `(3, 3k)` with `k ≥ 2`,
because `F_n(−1) > 0` for all `n ≥ 1`, `n ≠ 3`.

A second counterexample, `(11, 55)`, holds up under every reading of the conjecture's
"exceptional set E of primes p ≡ ±2 (mod 5)". The only prime factors of 11 and 55 are 5 and 11.
`gcd(F_55, F_11) = 1`, while `F_{gcd} = F_11` is monic of degree 25 with no
cyclotomic factor. `F_11(−1) = 3` does not divide `F_55(−1) = 121393`, so no
divisor of `F_55` is a multiple of `F_11`. No correction built from finitely
many primes or cyclotomic factors can turn `F_11` into `1`.

## Contents

- `report.tex`, `report.pdf`: the complete mathematical report.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent check using only Python 3's standard library. Gaussian binomials come
  from the product formula, the gcd from the Euclidean algorithm in `ℚ[q]`, and it
  also surveys all pairs `n < m ≤ 30`.
- `verification.txt`: the build log, axiom audit and Python output.

## Lean

Polynomials in `ℤ[q]` are coefficient lists, with `PEq` meaning equal coefficients.
`Dvd` is divisibility in `ℤ[q]`, and `IsGcd` is the standard gcd definition. `gauss` is
the Gaussian binomial. It is defined by the q-Pascal rule and checked against
the product formula for `n ≤ 7`. `qfib n` is the conjecture's sum.

- `isGcd_one` proves that `1` is a gcd of `F_6` and `F_3` in `ℤ[q]`, using a degree
  argument plus evaluation at `0` and `−1`.
- `conjecture_00000007672_false` proves `¬ GcdClause`. `GcdClause` says that for all
  `n, m ≥ 1`, every gcd of `F_n, F_m` is `F_{gcd(n,m)} · c` for some `c ∈ ℤ[q]`.
- `no_divisor_of_F6_is_multiple_of_F3` proves the stronger statement that no
  divisor of `F_6` is a multiple of `F_3`.
- `conjecture_00000007672_false_11_55` proves that for `(11, 55)` no gcd of `F_11` and `F_55`
  is `F_11 · c` (`GcdClauseExists` fails). It goes through
  `no_divisor_of_F55_is_multiple_of_F11`. `F_55(−1)` is computed by a proved-correct
  row-by-row evaluation of the Gaussian binomials.
- Not in Lean: the extension to correction factors in `ℚ[q]` (Gauss's lemma),
  `gcd(F_55, F_11) = 1`, and the fact that `F_11` has no cyclotomic factor. The report
  proves these and `verify.py` checks them.

The project has no `sorry`, no `native_decide`, and no added axioms.
`#print axioms` shows at most `propext`, `Classical.choice` and `Quot.sound`.
`qfib_mult3_at_neg_one` and `qfib_55_at_neg_one` use `decide +kernel`, which is
checked by the kernel.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想声称 q-Fibonacci 多项式 `F_n(q)=Σ_j [n−1−j choose j]_q q^{j²}` 在 `ℤ[q]` 中满足
`gcd(F_n,F_m) = F_{gcd(n,m)} × 修正因子`。取 `(n,m)=(6,3)`：
`F_3 = 1+q`，`F_6 = 1+q+q²+q³+2q⁴+q⁵+q⁶`。
由于 `F_3(−1)=0` 而 `F_6(−1)=2`，二者在 `ℤ[q]` 中的公因子只能是 `±1`，即 `gcd(F_6,F_3)=1`。
但 `gcd(6,3)=3`，若猜想成立，`1` 应是 `1+q` 的倍数；在 `q=−1` 处取值即得矛盾。
同理，对一切 `k≥2`，`(3,3k)` 都是反例。
更稳健的反例是 `(11,55)`：两者的素因子只有 5 和 11（都不 ≡ ±2 mod 5），`gcd(F_55,F_11)=1`，
而 `F_11` 是 25 次首一多项式且不含任何分圆因子，因此无论如何解读"例外集 E"，都无法由修正因子挽救。
Lean 项目从 Gaussian 二项式出发构造 `F_n`，证明 `1` 是 `F_6` 与 `F_3` 的最大公因子，
并证明猜想子句的否定。
