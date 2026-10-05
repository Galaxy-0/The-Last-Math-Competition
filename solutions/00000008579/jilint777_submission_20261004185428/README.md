# Disproof of conjecture 00000008579

The conjecture makes four claims about the Ornstein–Uhlenbeck (OU) operator on Wiener space:

1. the spectrum of `N = −L` is `{0, 1, 2, …}`;
2. **the multiplicity of the eigenvalue `n` is the partition number `p(n)`**;
3. the spectral counting function has Hardy–Ramanujan asymptotics;
4. the second-order correction is the Rademacher series.

Claim 2 is false, so the conjunction is false. Claim 1 is true, and the disproof does not need
claims 3 or 4.

## Counterexample

On cylinder polynomials the OU operator acts as `L = Σ_i (∂_i² − x_i ∂_i)`, where `x_i = W(e_i)`.

- `L x_0 = −x_0` and `L x_1 = −x_1`. So `W(e_0)` and `W(e_1)` are linearly independent
  eigenvectors for the eigenvalue 1, and `mult(1) ≥ 2 > 1 = p(1)`.
- **On Wiener space** (`dim H = ∞`, e.g. classical Wiener space) every eigenvalue `n ≥ 1` has
  infinite multiplicity. The squarefree products `x_{nj} ⋯ x_{nj+n−1}`, `j = 0, 1, 2, …`, are
  independent eigenvectors for `n`.
- **On `ℝ^d` with the Gaussian measure**, `mult(n) = C(n+d−1, d−1)`, the number of Hermite products
  `H_α` with `|α| = n`.

| n | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| p(n) | 1 | 1 | 2 | 3 | 5 | 7 |
| d = 1 | 1 | 1 | **1** | 1 | 1 | 1 |
| d = 2 | 1 | **2** | 3 | 4 | 5 | 6 |
| d = 3 | 1 | **3** | 6 | 10 | 15 | 21 |

The law therefore fails at `n = 1` or `n = 2` in every case:

| Space | Fails at | Why |
|---|---|---|
| `d = 0` (constants only) | `n = 1` | multiplicity 0, but `p(1) = 1` |
| `d = 1` | every `n ≥ 2` | each eigenspace is `ℝ·H_n`, and `p(n) ≥ 2` |
| `d ≥ 2` | `n = 1` | multiplicity `d` |
| Wiener space | every `n ≥ 1` | multiplicity `∞` |

Other readings (report, Section 4):

- **Field or kind of multiplicity.** Algebraic and geometric multiplicities agree (`N` is
  self-adjoint), and the answer is the same over ℚ, ℝ or ℂ.
- **Shifted indexing `p(n+s)`.** Fails in every case.
- **"For large `n`".** For finite `d`, `p(n)` is eventually larger than the polynomial
  `C(n+d−1, d−1)`. The proof uses `p(n) ≥ C(⌊n/(d+1)⌋+d, d)`. On Wiener space the multiplicities
  are infinite.
- **Symmetric functionals only.** The multiplicity is then the number of partitions of `n` into at
  most `d` parts. This fails at `n = d+1`, and on Wiener space it is 0 by Hewitt–Savage.
- **The weighted reading.** The operator `dΓ(diag(1,2,3,…)) = Σ_k k(∂_k² − x_k∂_k)` does have
  multiplicities `p(n)`, and **for it clause 2 holds**. The disproof is specific to the operator the
  statement names.
  - *For the weighted reading:* clauses 3 and 4 (Hardy–Ramanujan counting, Rademacher correction)
    only make sense with finite multiplicities. That is the strongest argument a reader could give.
  - *Against it, by definition:* in Malliavin calculus "the OU operator" is by definition
    `L = −δD`, i.e. `N = dΓ(I)` (Nualart §1.4).
  - *Against it, by canonicity:* on classical Wiener space there is no canonical `A` with spectrum
    `{1, 2, 3, …}`. The Brownian covariance has eigenvalues `((k−½)π)^(−2)` and the Cameron–Martin
    Laplacian has `((k−½)π)²`; neither is an integer.
  - So we treat `dΓ(diag(1,2,3,…))` as a different conjecture (report §4, item 6).

## Contents

- `report.tex` and `report.pdf`: the complete proof and the readings it covers.
- `lean4/`: a Lean 4.19.0 project (core library only).
- `verify.py` (Python 3 standard library): an independent check by a different method. It builds
  the matrix of `L` on monomials and computes `dim ker(L + n)` exactly over ℚ for `d = 1..4` and
  `n = 0..5`, plus the degree `≤ n+2` cross-check. It also checks the following:
  - Hermite `H_n` for `n ≤ 12`;
  - `p(n)` by two methods;
  - the shifted, eventual, symmetric and weighted-operator readings.
- `verification.txt`: a fresh `lake build` log with the axiom report, the forbidden-token scan
  and the output of `verify.py`.

## Lean

The following are defined from scratch:

- **Polynomials.** `Poly := (ℕ → ℕ) → ℤ` is the coefficient map. `IsPoly d` means finite support
  in `x_0, …, x_{d−1}`.
- **Operators.** `deriv i` is `∂_i`, `mulX i` is multiplication by `x_i`, and
  `L d f = Σ_{i<d} (∂_i∂_i f − x_i∂_i f)`.
- **Eigenvectors and multiplicity.** `Eig d n f` means `L f = −n f`. `LinIndep`, `MultGE` and
  `Mult` are multiplicity defined as the maximal number of independent eigenvectors.
- **Wiener space.** `EigCyl`, `MultGECyl` and `MultCyl` are the cylinder-polynomial versions.
- **Partitions.** `p` is the number of partitions.

Key theorems:

- `L_apply`: the coefficient formula. `deriv_mulX_comm`: `[∂_i, x_i] = 1`.
- `L_x0_x1`: `L x_0 = −x_0` and `L x_1 = −x_1`. `linIndep_x`: the `x_i` are independent.
- `eig_H2`: `L(x²−1) = −2(x²−1)` (non-vacuity).
- `eig1_prop`: in one variable, any two eigenvectors for the same eigenvalue are proportional,
  whatever their degree. From it:
  - `mult1_le`: `mult_1(n) ≤ 1` for all `n`;
  - `eig2_eq_H2`: every eigenvector for 2 is `c·(x²−1)`;
  - `mult1_exact`: the multiplicities of 0, 1, 2 are exactly 1.
- `multGE_blocks`: `mult_d(n) ≥ m` whenever `n·m ≤ d`.
- `p_values`: `p(0..5) = 1, 1, 2, 3, 5, 7`, proved by `decide +kernel` (checked by the kernel, not
  `native_decide`). `p_ge_two`: `p(n) ≥ 2` for `n ≥ 2`.
- **`partitionLaw_false d : ¬ PartitionLaw d` for every `d`.** `d1_fails_all` covers every
  `n ≥ 2` for `d = 1`.
- `L_eq_of_isPoly`: `L` is consistent across dimensions. `multCyl_infinite`: on Wiener space no
  `n ≥ 1` has finite multiplicity. `partitionLawCyl_false`.
- **`conjecture_00000008579_false`** and **`conjecture_00000008579_false_wiener`**:
  `¬ (C1 ∧ PartitionLaw ∧ C3 ∧ C4)` for arbitrary propositions C1, C3, C4.

The project has no `sorry`, no `native_decide` and no added axioms. `#print axioms` reports
`propext`, `Classical.choice` and `Quot.sound`. Classical choice is used only to decide equality of
multi-indices in the definition of monomials.

Limitations:

- Lean works on the polynomial core. It does not formalize `L²(μ)`, the closure of `L`, or Hermite
  completeness.
- For `d ≥ 2` and for Wiener space only lower bounds are needed, and polynomial eigenvectors are
  genuine eigenvectors of `N`.
- For `d = 1`, the upper bound `mult(2) ≤ 1` is proved in Lean for polynomial eigenvectors. Its
  extension to all of `L²(γ₁)` uses Hermite completeness and is proved in the report only.
- The following are in the report and `verify.py` only: the general-`n` existence of `H_n`, the
  exact formula `C(n+d−1, d−1)`, and the readings with shifts, eventual equality or symmetric
  functionals.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想对维纳空间上的 Ornstein–Uhlenbeck 算子断言四件事：
（1）N = −L 的谱为非负整数；（2）**本征值 n 的重数为分拆数 p(n)**；
（3）谱计数函数服从 Hardy–Ramanujan 渐近；（4）第二项修正为 Rademacher 级数。
第（2）条不成立，因此整个合取命题不成立。第（1）条是正确的，证明不需要第（3）、（4）条。

在柱多项式上，OU 算子作用为 L = Σ_i (∂_i² − x_i ∂_i)，其中 x_i = W(e_i)。
由 L x_0 = −x_0、L x_1 = −x_1 可知，W(e_0)、W(e_1) 是本征值 1 的两个线性无关的本征向量，
所以 mult(1) ≥ 2 > 1 = p(1)。

- 在无穷维维纳空间（如经典维纳空间）上：每个 n ≥ 1 的重数都是无穷，
  因为无平方因子的乘积 x_{nj}⋯x_{nj+n−1} 给出无穷多个线性无关的本征向量。
- 在带高斯测度的 ℝ^d 上：重数为 C(n+d−1, d−1)（|α| = n 的 Hermite 乘积的个数）。
  - d ≥ 2 时 mult(1) = d ≥ 2，在 n = 1 处不成立；
  - d = 1 时每个本征空间都是 ℝ·H_n，重数为 1，而 n ≥ 2 时 p(n) ≥ 2，
    因此在 n = 2 及之后的每个 n 处都不成立；
  - d = 0 时 mult(1) = 0 ≠ 1。

同一结论对下列理解都成立：
- 平移指标 p(n+s)；
- "对充分大的 n 成立"：有限维时重数是多项式，而 p(n) ≥ C(⌊n/(d+1)⌋+d, d) 增长更快；无穷维时重数为无穷；
- 只取对称泛函：重数为"至多 d 个部分的分拆数"，在 n = d+1 处不成立；无穷维时由 Hewitt–Savage 定律为 0；
- 在 ℚ、ℝ 或 ℂ 上计数，代数重数或几何重数（N 自伴，两者相同）。

加权算子 dΓ(diag(1,2,3,…)) = Σ_k k(∂_k² − x_k∂_k) 的重数确实是 p(n)，**对它第（2）条成立**，
所以本反证只针对题目所指的算子。
- 支持加权理解的最强理由是：第（3）、（4）条（Hardy–Ramanujan 计数、Rademacher 修正）只在重数有限时才有意义。
- 但按定义，Malliavin 分析中"OU 算子"就是 L = −δD，即 N = dΓ(I)（Nualart §1.4）。
- 而且在经典维纳空间上不存在谱为 {1,2,3,…} 的典范算子 A：布朗运动协方差算子的本征值为 ((k−½)π)^(−2)，
  Cameron–Martin 空间上 Laplace 算子的本征值为 ((k−½)π)²，都不是整数。
- 因此我们把加权算子视为另一个猜想（见报告第 4 节第 6 条）。

Lean 部分（仅核心库）从零定义了：
- 多项式（系数映射）；
- 偏导数 ∂_i、乘以 x_i 的算子，以及 L = Σ(∂_i² − x_i∂_i)；
- 本征向量、线性无关、重数（含柱多项式版本）和分拆数 p(n)。

主要结果：
- `partitionLaw_false`：对每个维数 d，分拆重数律都不成立；
- `partitionLawCyl_false`：在维纳空间上分拆重数律不成立（每个 n ≥ 1 重数无穷）；
- `conjecture_00000008579_false` 与 `conjecture_00000008579_false_wiener`：
  对第（1）、（3）、（4）条取任意命题，合取都不成立；
- 非空性：L(x²−1) = −2(x²−1)，以及单变量下任意次数的本征向量必与 H_n 成比例。

局限：
- Lean 只在多项式核上工作；
- d = 1 时把上界推广到整个 L²(γ₁)（需要 Hermite 完备性），只在报告中证明。

`verify.py` 用不同的方法（单项式基上的精确有理线性代数）独立验证了上述重数表以及各种理解。
