# Disproof of conjecture 00000001196

**Conjecture:** let `M(λ,μ)` be the largest Littlewood–Richardson coefficient `N^ν_{λμ}`
of Schur Q-functions. Then `M(λ,μ) ≤ min(2^{ℓ(λ)}, 2^{ℓ(μ)}, f^ν)`, and at `λ = μ = (k)`
the value is exactly `2^{k−1}`.

**Answer: false.** For every `k ≥ 1`,

```
Q_(k) Q_(k) = 2 Σ_{j=0}^{k−1} Q_(2k−j, j)        P_(k) P_(k) = P_(2k) + 2 Σ_{j=1}^{k−1} P_(2k−j, j)
```

So `M((k),(k)) = 2` for every `k ≥ 2` in both standard normalisations: Stembridge's
shifted LR coefficients `P_λ P_μ = Σ f^ν_{λμ} P_ν`, and the Q-basis structure constants.
It is never `2^{k−1}` once `k ≥ 3`. The smallest counterexample is `k = 3`:

```
Q_3 Q_3 = 2 Q_6 + 2 Q_51 + 2 Q_42,     P_3 P_3 = P_6 + 2 P_51 + 2 P_42,     M((3),(3)) = 2 ≠ 4.
```

(`k = 1, 2` agree with the claim.) We also check every mixed normalisation: `X_(k) Y_(k)`
expanded in the `Z`-basis, with `X, Y, Z ∈ {P, Q}`. At `k = 3` the eight readings give
`M((3),(3)) ∈ {2, 2, 4, 4, 1, 1, 8, 1/2}`. The only readings that give the claimed `4` are
`P_3·Q_3` and `Q_3·P_3` in the P-basis. They violate the bound clause, which implies
`M((k),(k)) ≤ 2^{ℓ((k))} = 2` whatever `f^ν` means. So the conjecture fails at `λ = μ = (3)`
under every reading. In fact its two clauses contradict each other for every `k ≥ 3`.

## Contents

- `report.tex`, `report.pdf`: the complete argument. It contains a hand proof of the
  identity for all `k`, a table of `M((k),(k))` for every reading, and the explicit
  three-variable computation at `k = 3` with the uniqueness argument.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent check using only Python 3's standard library. It builds
  `Q_ν` and `P_ν` from marked shifted tableaux, compares them with the Pfaffian definition
  used in Lean, and expands all products for `k = 1..5` by exact rational linear algebra.
- `verification.txt`: the fresh build log, forbidden-token scan and Python output.

## Lean

Everything is built from scratch in `ℤ[x₁,x₂,x₃]`. Polynomials are lists of
(exponent, coefficient) pairs, and `coeff` gives the total coefficient of a monomial.

- `q r` is the coefficient of `t^r` in `∏_{i≤3} (1+x_i t)/(1−x_i t)`.
- `Q2 r s = q_r q_s + 2 Σ_{i=1}^{s} (−1)^i q_{r+i} q_{s−i}`.
- `Qfun ν` is Schur's Pfaffian (Macdonald III.8).
- `Pfun ν = 2^{−ℓ(ν)} Qfun ν`. `P_exact` proves the division is exact.
- `q_relation` proves `Σ (−1)^i q_i q_{r−i} = 0` for `r ≤ 6`, and `Q321_eq` gives the product
  formula for `Q_321`.
- `Expands d T cs B` means `d·T = Σ cs_i B_i` coefficientwise. `ValueAt k X Y Z` says the
  largest coefficient of `X_(k) Y_(k)` in the `Z`-basis is `2^{k−1}`. `BoundAt k X Y Z` says
  every expansion has largest coefficient `≤ 2^{ℓ((k))}`. `Conjecture X Y Z` is
  `∀ k ≥ 1, ValueAt ∧ BoundAt`.
- `QQ_in_Q`, `PP_in_P` and six more: the expansions at `k = 3` as polynomial identities.
- `expansion_exists` shows non-vacuity. `solveQ`, `solveP` and `expansion_unique` prove the
  coefficients are unique, by triangularity at four monomials. `max_coeff` gives the value
  of `M((3),(3))` for each reading.
- `value_clause_false_P` and `value_clause_false_Q` prove `¬ ∀ k ≥ 1, ValueAt k` in the two
  standard readings.
- **`conjecture_00000001196_false : ∀ X Y Z, ¬ Conjecture X Y Z`**.
- `bound_holds_P` and `value_holds_PQP` show that neither predicate is trivially false.

Not in Lean: the identity for general `k` and the passage from three variables to the full
ring `Γ`. The report proves both, and `verify.py` checks the identity for `k ≤ 5`. At
`k = 3` three variables are faithful: specialisation is a ring homomorphism, all strict
partitions of 6 have at most 3 parts, and the four `Q_ν` are proved linearly independent.

The project has no `sorry`, no `native_decide`, and no added axioms. `#print axioms` shows
at most `propext` and `Quot.sound`. The computations use `decide +kernel`, which is checked
by the kernel. A fresh build takes about one minute.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想定义 `M(λ,μ)` 为 Schur Q-函数乘积的 Littlewood–Richardson 系数 `N^ν_{λμ}` 的最大值，
并断言 `M(λ,μ) ≤ min(2^{ℓ(λ)}, 2^{ℓ(μ)}, f^ν)`，且在 `λ=μ=(k)` 时恰为 `2^{k−1}`。

**结论：猜想不成立。** 对一切 `k ≥ 1` 有
`Q_(k)Q_(k) = 2 Σ_{j=0}^{k−1} Q_(2k−j,j)` 及 `P_(k)P_(k) = P_(2k) + 2 Σ_{j=1}^{k−1} P_(2k−j,j)`
（报告中给出手写证明）。因此在两种标准归一化（Stembridge 的移位 LR 系数 `f^ν_{λμ}` 与 Q-基结构常数）下，
`k ≥ 2` 时 `M((k),(k)) = 2`。最小反例是 `k = 3`：`Q_3Q_3 = 2Q_6 + 2Q_51 + 2Q_42`，
`M((3),(3)) = 2 ≠ 4`（`k = 1, 2` 时与猜想一致）。
我们还检查了全部八种混合归一化读法（`X_(k)Y_(k)` 在 `Z`-基下展开，`X,Y,Z ∈ {P,Q}`）。
`k = 3` 时只有 `P_3·Q_3`（或 `Q_3·P_3`）在 P-基下给出 4，但这违反了猜想自身的界
`M ≤ 2^{ℓ((3))} = 2`（无论 `f^ν` 指什么，该界都蕴含此式）。所以在每一种读法下猜想都在 `λ=μ=(3)` 处失败。
事实上，对 `k ≥ 3`，猜想的两个子句彼此矛盾。

Lean 项目只用核心库，在 `ℤ[x₁,x₂,x₃]` 中从生成函数 `∏(1+x_i t)/(1−x_i t)` 构造 `q_r`，
用 Schur 的 Pfaffian 构造 `Q_ν`，并令 `P_ν = 2^{−ℓ(ν)}Q_ν`。它证明了 `k=3` 的全部展开式，
用三角性证明展开系数唯一，并证明主定理 `conjecture_00000001196_false`。
`verify.py` 用带标记移位杂表（marked shifted tableaux）独立地重新计算全部结果。
一般 `k` 的恒等式及从三个变量到环 `Γ` 的过渡没有在 Lean 中形式化，由报告给出证明。
