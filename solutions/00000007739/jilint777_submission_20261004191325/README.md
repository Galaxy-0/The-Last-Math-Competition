# Disproof of conjecture 00000007739

The conjecture says: for free words `W` of length `d` in a free semicircular family, with
`M_p(d) = ‖W‖_p / ‖W‖_2`,

- **(C1)** `M_4(d)^2 = f(d) := 2 − d⁻¹(1 − 2^{−d})`, and
- **(C2)** an informal statement about `M_∞(d)/M_p(d)` and free group generators.

Clause (C1) is false, so the conjunction is false whatever (C2) means.

## Counterexample (`d = 1`)

A free word of length 1 is a single standard semicircular `s`. Realise it on the full Fock space
as `s = ℓ(e₀) + ℓ(e₀)*` with the vacuum state `τ = ⟨Ω, ·Ω⟩`:

- `sΩ = e₀`, so `‖s‖₂² = τ(s²) = 1`;
- `s²Ω = e₀⊗e₀ + Ω`, so `‖s‖₄⁴ = τ(s⁴) = ‖s²Ω‖² = 2`.

So `M_4(1)⁴ = 2` and `M_4(1)² = √2 ≈ 1.414`. The formula gives `f(1) = 3/2`, and if
`M_4(1)² = 3/2` then `M_4(1)⁴ = 9/4 ≠ 2`.

## Readings covered (report, Sections 4–6)

- **Normalisation.** `M_4(1)` is `2^{1/4}`, `M_4(1)²` is `√2` and `M_4(1)⁴` is `2`; none of
  them equals `3/2`.
- **Optimal constant (sup), inf, or any attained value, real or complex coefficients.** Every
  nonzero `S = Σ cᵢ sᵢ` in the first chaos has `‖S‖₄⁴ = 2‖S‖₂⁴`, because
  `S*SΩ = Σ c̄ᵢcⱼ eᵢ⊗eⱼ + (Σ|cᵢ|²)Ω`. Circular and elliptic elements are included. So the ratio
  is constant at `d = 1`.
- **All `d`.** For `W = s₁⋯s_d`, `‖W‖₂ = 1` and `‖W‖₄⁴ = d + 1` (Fuss–Catalan, proved by
  counting non-crossing pairings).
  - `M_4(d)⁴ = d+1` is an integer, while `f(d) = (2d·2^d − 2^d + 1)/(d·2^d)` has negative 2-adic
    valuation. So none of `M_4 = f`, `M_4² = f` or `M_4⁴ = f` holds for any `d ≥ 1`.
  - On the `d`-th chaos the ratio `‖x‖₄⁴/‖x‖₂⁴` is always `≥ 2`. Its infimum is `2` and its
    supremum is `≥ d+1`, while `9/4 ≤ f(d)² < 4` and `f(2)² = 169/64 < 3`.
- **Haar unitaries / free group generators.** A word is unitary, so `M_p = 1`. For combinations
  `Σ a_s λ(s)` the ratio is `2 − Σ|a_s|⁴/(Σ|a_s|²)² ∈ [1, 2)`. Disclosure: `u + u*` (arcsine law)
  has `M_4⁴ = 3/2 = f(1)`. That value is neither the optimal constant (`sup = 2`) nor the
  semicircular value the conjecture is about.
  - **Other free-group analogues** were searched as well, all checked exactly in `verify.py`:
    `Σ(u_i+u_i*)` gives `2 − 1/(2d)`, `Π(u_i+u_i*)` gives `1 + d/2`, free Bernoulli sums give
    `2 − 1/d`, and so do sums of all reduced words of length `d` in `F_2` or `Z_2*Z_2*Z_2`.
    None of them reproduces `f(d)` (or `f(d)²`, `f(d)⁴`) beyond `d = 1`.
- **Disclosed coincidence: the non-centred element `1 + s`.** `τ((1+s)²) = 2` and
  `τ((1+s)⁴) = 1 + 6 + 2 = 9`. So `‖1+s‖₄⁴/‖1+s‖₂⁴ = 9/4`, which gives `M_4² = 3/2 = f(1)`
  exactly. It does not rescue the conjecture, for three reasons:
  - (a) `1 + s` is not a free word of length 1 (it is not even centred).
  - (b) The optimal constant over `a + Σ cᵢsᵢ` (complex coefficients) is `sup = 7/3`, attained at
    `|a|²/|c|² = 1/2` (e.g. `1 + s₁ + s₂`). That is not `9/4` (report, Section 6).
  - (c) The natural length-`d` extensions fail at `d = 2`. `1 + s₁s₂` has ratio `2`; in general
    `1 + s₁⋯s_d` has ratio `(d+6)/4` for `d ≥ 2`. `Π(1+sᵢ)` has ratio `1 + 5d/4 = 7/2` at `d = 2`.
    Both differ from `f(2)² = 169/64`, and by 2-adic valuation they never match for `d ≥ 2`.

## Contents

- `report.tex`, `report.pdf`: the complete proof and the readings it covers.
- `lean4/`: a Lean 4.19.0 project, core library only.
- `verify.py`: a Python 3 standard-library check with exact arithmetic.
- `verification.txt`: a fresh `lake build` log with the axiom report, the forbidden-token scan
  and the output of `verify.py`.

## Lean

Defined from scratch:

- Fock-space basis words and finitely supported vectors, with `coeff` and `inner`.
- Creation `ℓ(e_i)` and annihilation `ℓ(e_i)*`, `X_i = ℓ(e_i) + ℓ(e_i)*`, the vacuum `Ω` and
  `τ = ⟨Ω, ·Ω⟩`.

Key theorems:

- Adjointness: `inner_create`, `inner_annih`, `X_selfadjoint`, and `applyW_adjoint` (the adjoint
  of a monomial is the reversed monomial).
- The norms: `norm2sq_eq`, `norm4pow4_eq` (`‖W‖₂² = ‖WΩ‖²` and `‖W‖₄⁴ = ‖W*WΩ‖²`).
- `semicircle_moments`: the moments of `X₀` are Catalan numbers, up to degree 10.
- `word1`: `‖X₀‖₂² = 1` and `‖X₀‖₄⁴ = 2`.
- `words_234`: `‖X₀⋯X_{d−1}‖₄⁴ = d+1` for `d = 2, 3, 4`.
- `first_chaos_three`: `τ(S⁴) = 2τ(S²)²` for all `S = aX₀ + bX₁ + cX₂`, as a polynomial identity.
- `first_chaos_never_formula`: no nonzero first-chaos element has ratio `9/4`, `3/2` or `81/16`.
- `clause_false_d1`, and `clause_false_small` (all three normalisations fail for `d = 1..4`).
- **`conjecture_00000007739_false (C2) : ¬ (Conj ∧ C2)`.**

`M_4(d)² = f(d)` is encoded exactly, without real numbers: since `f(d) > 0`, it is equivalent to
`f(d)² = ‖W‖₄⁴/‖W‖₂⁴`, cleared of denominators.

The project has no `sorry` and no `native_decide`. The axioms used are at most `propext` and
`Quot.sound`. Two theorems (`semicircle_moments`, `first_chaos_three`) are preceded by
`set_option maxRecDepth 100000 in`. This only raises the elaborator's recursion limit for the
`decide`/`simp` unfolding of the list computations; it is harmless and adds no axioms.

Limitations: the following are in the report only:

- freeness of the `X_i` (Voiculescu's theorem) and the passage to `L^p` norms of the von
  Neumann algebra;
- complex coefficients;
- the proof for general `d`;
- the higher-chaos and unitary readings.

`verify.py` checks all of these numerically and exactly.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想断言：对自由半圆族生成的长度为 d 的自由字 W，记 M_p(d) = ‖W‖_p/‖W‖_2，则
**M_4(d)² = 2 − d⁻¹(1 − 2^{−d})**，并附带一条关于 M_∞(d)/M_p(d) 与自由群生成元的模糊陈述。
前一条不成立，因此整个合取命题不成立，与第二条的含义无关。

**反例（d = 1）。** 长度为 1 的自由字就是一个标准半圆元 s。在完全 Fock 空间上取
s = ℓ(e₀) + ℓ(e₀)*，τ 为真空态：
- sΩ = e₀，故 ‖s‖₂² = 1；
- s²Ω = e₀⊗e₀ + Ω，故 ‖s‖₄⁴ = τ(s⁴) = 2。

所以 M_4(1)⁴ = 2，M_4(1)² = √2。公式给出 3/2，而 (3/2)² = 9/4 ≠ 2。

**各种理解都被否定：**
- 无论把 M_4、M_4² 还是 M_4⁴ 与公式比较，都不相等。
- 若把 M_p(d) 理解为"比率的最优常数"（上确界），或下确界，或任一取到的值，结论不变：
  第一混沌中任一非零元 S = Σ cᵢ sᵢ（实系数或复系数，包括圆元、椭圆元）都满足
  ‖S‖₄⁴ = 2‖S‖₂⁴，比率是常数。
- 对一般 d，取 W = s₁⋯s_d，有 ‖W‖₄⁴ = d + 1（Fuss–Catalan 数，由非交叉配对计数证明）。
  这是整数，而 f(d) 的 2-adic 赋值为负，因此任何 d ≥ 1、任何归一化下等式都不成立。
- 在 d 阶混沌上比率恒 ≥ 2，下确界为 2，上确界 ≥ d+1，都不等于 f(d)²。
- 若理解为 Haar 酉元（自由群生成元）的字：字是酉元，M_p = 1。线性组合的比率落在 [1, 2) 内。
  需要说明的是，u + u*（反正弦分布）的 M_4⁴ 恰为 3/2，但这既不是最优常数，也不是猜想所说的半圆情形。
- 我们还检验了其他自由群类比，均在 `verify.py` 中精确验证：Σ(u_i+u_i*) 给出 2 − 1/(2d)，
  Π(u_i+u_i*) 给出 1 + d/2，自由 Bernoulli 和给出 2 − 1/d，F_2 或 Z_2*Z_2*Z_2 中长度为 d 的全部既约字之和也一并检验。
  d ≥ 2 时没有一个能重现 f(d)。
- **需披露的巧合：非中心化元 1 + s。** τ((1+s)²) = 2，τ((1+s)⁴) = 1 + 6 + 2 = 9，
  比率为 9/4，即 M_4² = 3/2 = f(1)，恰好相等。但这不能挽救猜想，原因有三：
  - (a) 1 + s 不是长度为 1 的自由字（甚至不是中心化的）；
  - (b) 在 a + Σ cᵢsᵢ 这一类中，最优常数（上确界）为 7/3，在 |a|²/|c|² = 1/2 处取到（例如 1 + s₁ + s₂），不是 9/4；
  - (c) 自然的长度 d 推广在 d = 2 时即不成立：1 + s₁s₂ 的比率为 2（一般地，d ≥ 2 时 1 + s₁⋯s_d 的比率为 (d+6)/4），
    Π(1+sᵢ) 的比率为 1 + 5d/4，d = 2 时为 7/2，均不等于 f(2)² = 169/64。由 2-adic 赋值可知 d ≥ 2 时都不会相等。

**Lean 部分（仅核心库）**从零构造了：
- 完全 Fock 空间的有限支撑向量与内积；
- 产生算子、湮灭算子、X_i = ℓ(e_i) + ℓ(e_i)*，以及真空态 τ。

证明了：
- 伴随关系，X_i 自伴，单项式的伴随是反序单项式；
- 范数公式；
- X₀ 的各阶矩为 Catalan 数；
- ‖X₀‖₄⁴ = 2，以及 d = 2, 3, 4 时 ‖X₀⋯X_{d−1}‖₄⁴ = d + 1；
- 第一混沌中 τ(S⁴) = 2τ(S²)²（三个生成元，作为多项式恒等式）；
- 最终定理 `conjecture_00000007739_false : ¬ (Conj ∧ C2)`。

Lean 中有两处 `set_option maxRecDepth 100000 in`，仅提高展开列表计算时的递归深度上限，无害，不引入公理。

局限：自由性（Voiculescu 定理）、复系数、一般 d、高阶混沌及酉元理解只在报告中证明，
并由 `verify.py` 用两种独立方法（Fock 空间稀疏算子、非交叉配对计数）精确验证。
