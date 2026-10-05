# Disproof of conjecture 00000003831

The conjecture is a conjunction of two clauses:

- **(C1)** For any finite crystal `B`, the coefficients of the Schur expansion of the Weyl
  symmetrization of `ch(B)` are nonnegative.
- **(C2)** For `B = B(λ) ⊗ B(μ)` these coefficients are the Littlewood–Richardson coefficients.

**(C1) is false**, so the conjecture is false. (C2) is true under the Weyl-symmetrizer reading:
`ch(B(λ)⊗B(μ)) = s_λ s_μ` is symmetric, so the symmetrizer fixes it. The disproof rests on (C1) alone.

## Counterexample: a 7-vertex seminormal `gl₃` crystal `B7`

Take `B(2,1,0)`, identify its two vertices of weight `(1,1,1)` into one vertex `Z`, and keep all
eight edges. The result has the following vertices (weights in brackets):

`A(2,1,0) B(1,2,0) C(2,0,1) D(0,2,1) E(1,0,2) F(0,1,2) Z(1,1,1)`

and the following edges:

- `f̃₁`: `A→B`, `C→Z→D`, `E→F`;
- `f̃₂`: `A→C`, `B→Z→E`, `D→F`.

`ε_i` and `φ_i` are the string lengths.

- **It is a crystal, and seminormal.** All of Kashiwara's axioms hold: `f̃_i b = b' ⇔ ẽ_i b' = b`,
  `wt(f̃_i b) = wt b − α_i`, `ε` and `φ` shift by ±1 along edges, and `φ_i − ε_i = ⟨h_i, wt⟩`.
  Seminormality holds by construction: `ε_i(b) = max{k : ẽ_iᵏ b ≠ 0}`, and likewise for `φ_i`.
  `B7` is connected.
- **Its character is not Schur positive.**
  `ch(B7) = m₂₁ + m₁₁₁ = s₂₁ − s₁₁₁`, because `s₂₁ = m₂₁ + 2m₁₁₁`. This expansion is unique.
- **Every symmetrization reading fails.** `ch(B7)` is symmetric, so:
  - the Weyl symmetrizer `J(x^ρ f)/J(x^ρ)` (the Demazure operator `π_{w₀}`) gives `s₂₁ − s₁₁₁`;
    equivalently `J(x^ρ ch) = a₄₂₀ − a₃₂₁`;
  - the orbit sum gives `6s₂₁ − 6s₁₁₁`;
  - the orbit average gives `s₂₁ − s₁₁₁`.

  The coefficient of `s₁₁₁` is negative in each case. The same holds for `sl₃`:
  `ch = χ_(1,1) − χ_(0,0)`.

### Boundary of the counterexample

- **Normal crystals.** For normal (Stembridge) crystals (C1) is true: `B ≅ ⊔ B(λ)`, so `ch B = Σ s_λ`.
  `B7` is therefore not normal. Only normal-type readings rescue (C1): "finite crystal =
  normal crystal", or the affine-theory term "finite crystal". The latter means crystal bases of
  finite-dimensional `U'_q(ĝ)`-modules, such as Kirillov–Reshetikhin or perfect crystals, and
  these are classically normal.
- **The symmetrization would be idle for normal crystals.** For normal (indeed seminormal)
  crystals `ch(B)` is already `W`-invariant. So "Weyl symmetrization" would be vacuous, and (C1)
  would be a triviality. The explicit symmetrization therefore points to the abstract notion,
  under which even a 1-vertex crystal is a counterexample (see the remark below). `B7` refutes
  (C1) even under the stronger seminormal reading. The standard references define "crystal" abstractly,
  with seminormal and normal as extra conditions: Kashiwara 1993 and 1995, and Bump–Schilling 2017, Ch. 2.
- **`gl₂` has no counterexample.** Every finite seminormal `gl₂` crystal is a disjoint union of
  strings, and each string has character `s_(a,c)`.
- **7 vertices is minimal for `gl₃`.** Characters of seminormal crystals are exactly the
  `S₃`-invariant weight multisets that satisfy the string condition. Among those with at most 6
  vertices there are 12, all Schur positive. With 7 vertices the only non-positive one, up to a
  `det` shift, is `ch(B7)`. This is checked by exhaustive search.
- **Remark.** Without seminormality, one vertex suffices:
  - the abstract `gl₂` crystal `{b}` with `wt b = (−1,2)`, `ε = 3`, `φ = 0` has Weyl
    symmetrization `−s₁₀`;
  - the lowest vertex of `B(2,0)`, alone with its inherited `ε = 2`, `φ = 0`, has character `x₂²`
    and Weyl symmetrization `−s₁₁` (orbit sum `x₁² + x₂² = s₂₀ − s₁₁`).

## Contents

- `report.tex`, `report.pdf`: the complete proof, the readings covered, and the minimality and
  `gl₂` arguments.
- `lean4/`: a Lean 4.19.0 project, core library only. It has no `sorry` and no `native_decide`.
  The main theorems depend only on `propext` and `Quot.sound`.
- `verify.py`: an independent check in Python 3 using only the standard library. It covers:
  - the crystal axioms, checked by walking the strings;
  - Schur polynomials computed both from tableaux and by exact bialternant division;
  - the symmetrizer, computed by exact division and also via Demazure operators;
  - the orbit sum and the orbit average;
  - the `gl₂` search (up to 10 vertices) and the `gl₃` minimality search (up to 7 vertices),
    including an explicit realisation of the 7-vertex character;
  - sanity checks on the normal crystals `B(1,0,0)`, `B(2,1,0)` and `B(1)^⊗3`.
- `verification.txt`: the fresh build log, the axiom report, the forbidden-token scan and the
  output of `verify.py`.

## Lean

Everything is defined from scratch:

- `Crystal n` on `Fin n`, with `wt : Fin n → ℤ³`, `e i, f i : Fin n → Option (Fin n)` and
  `eps i, phi i : Fin n → ℤ`.
- `IsCrystal`: Kashiwara's axioms.
- `IsSeminormal`. The lemmas `seminormal_eps_max` and `seminormal_phi_max` show that it
  means "`ε` and `φ` are the maximal string lengths".
- Laurent polynomials, with coefficient-wise equality `PolyEq` and a proved-correct decision
  procedure. On top of these: `mul`, the `S₃` action, the antisymmetrizer `J`, the orbit sum
  `orb`, and the character `ch`.
- `schur λ`: the sum over semistandard tableaux. The bialternant identities `s_λ a_ρ = a_{λ+ρ}`
  are checked for `λ ⊢ 3`. `schur3_indep` proves that degree-3 Schur expansions are unique.
- `WeylSym f q :≡ q · J(x^ρ) = J(x^ρ f)`, and `schurCoeffW f λ = [x^{λ+ρ}] J(x^ρ f)`.

Main results:

- `B7_counterexample`: `B7` is a seminormal crystal, `WeylSym (ch B7) (ch B7)` holds,
  `ch B7 = s₂₁₀ − s₁₁₁`, and every Weyl symmetrization of `ch B7` has coefficient `−1` at
  `s₁₁₁` in every Schur expansion (`weyl_forced`).
- **`conjecture_00000003831_false : ¬ ClaimWeyl`**, where
  `ClaimWeyl := ∀ n (B : Crystal n), B.IsCrystal → B.IsSeminormal → ∀ q, WeylSym (ch B) q → ∀ a b c, Expands q a b c → 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c`.
- The variants `_abstract` (no seminormality), `_bialt` (coefficient `[x^{λ+ρ}]J(x^ρ ch)` for
  every dominant `λ`), `_orbit` and `_avg`. The last uses `6q = Σ_w w(ch)`.
- Non-vacuity:
  - `B100_ok`: `B(1,0,0)` is a seminormal crystal with character `s₁₀₀`;
  - `B210_ok`: `B(2,1,0)` satisfies all hypotheses, with expansion `s₂₁₀ ≥ 0`;
  - `broken_rejected`: a datum that violates `φ − ε = ⟨h, wt⟩` is rejected.

Limitations:

- In Lean the quantified Schur expansions are the degree-3 ones. This is enough because
  `ch B7` is homogeneous of degree 3; general uniqueness is proved in the report.
- "The symmetrizer fixes symmetric `f`" is checked for `ch B7` but not proved in general.
- Normality, the classification of seminormal characters, the `gl₂` statement and minimality
  are proved in the report and checked in `verify.py`, not in Lean.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想由两部分组成：
（C1）对任意有限晶体 B，ch(B) 的 Weyl 对称化的 Schur 展开系数非负；
（C2）当 B = B(λ)⊗B(μ) 时，这些系数恰为 LR 系数。
我们否定（C1），因此整个猜想不成立。在 Weyl 对称化算子的解释下（C2）是成立的：ch(B(λ)⊗B(μ)) = s_λ s_μ 是对称多项式，被对称化算子保持不变。所以本否证只依赖（C1）。

反例是一个 7 顶点的半正规（seminormal）gl₃ 晶体 B7。构造方法：在 B(2,1,0) 中把两个权为 (1,1,1) 的顶点合并为一个顶点 Z，八条边全部保留。
- 顶点及其权：A(2,1,0)、B(1,2,0)、C(2,0,1)、D(0,2,1)、E(1,0,2)、F(0,1,2)、Z(1,1,1)。
- f̃₁ 的边：A→B、C→Z→D、E→F。
- f̃₂ 的边：A→C、B→Z→E、D→F。
- ε_i、φ_i 取弦长。

B7 满足 Kashiwara 晶体的全部公理，并且是半正规、连通的。
其字符为 ch(B7) = m₂₁ + m₁₁₁ = s₂₁ − s₁₁₁，Schur 展开唯一。ch(B7) 是对称多项式，因此：
- Weyl 对称化算子 J(x^ρ f)/J(x^ρ)（即 Demazure 算子 π_{w₀}）给出 s₂₁ − s₁₁₁；
- 轨道和给出 6s₂₁ − 6s₁₁₁；
- 轨道平均给出 s₂₁ − s₁₁₁。

三种解释下 s₁₁₁ 的系数都是负数。换成 sl₃ 的说法同样成立：ch = χ_(1,1) − χ_(0,0)。

反例的边界：
- 对正规（Stembridge）晶体，（C1）成立，因为 ch B = Σ s_λ。所以只有"正规型"的解释才能挽救（C1）：一是把"有限晶体"理解为"正规晶体"；二是仿射理论中的"有限晶体"，即有限维 U'_q(ĝ) 模的晶体基（如 Kirillov–Reshetikhin 晶体、完美晶体），它们在经典部分上是正规的。
- 对称化在正规晶体上是空操作：对正规（乃至半正规）晶体，ch(B) 本身已经 W 不变，"Weyl 对称化"不起任何作用，（C1）也就成了平凡命题。因此题中明确写出对称化，说明它指的是抽象晶体；在这一意义下连 1 个顶点的晶体都是反例。而 B7 在更强的半正规解释下也否定了（C1）。
- 标准文献把晶体定义为抽象对象，半正规、正规都是附加条件：Kashiwara 1993、1995；Bump–Schilling 2017 第 2 章。
- gl₂ 的半正规晶体不可能给出反例：每条弦的字符就是一个 s_(a,c)。
- 对 gl₃，半正规晶体的字符恰为满足弦条件的 S₃ 不变权多重集。顶点数不超过 6 的共 12 个，全部 Schur 正。所以 7 个顶点是最小的，并且在相差一个 det 平移的意义下，7 顶点的反例字符唯一，就是 ch(B7)。
- 附注：若不要求半正规，一个顶点即可构成反例。
  - 取 gl₂ 晶体 {b}，wt b = (−1,2)，ε = 3，φ = 0，其 Weyl 对称化为 −s₁₀。
  - 取 B(2,0) 的最低顶点单独成晶体，保留继承的 ε = 2、φ = 0。其字符为 x₂²，Weyl 对称化为 −s₁₁。

Lean 部分（4.19.0，仅核心库，无 sorry、无 native_decide）从零定义了以下对象：
- 晶体结构与 Kashiwara 公理；
- 半正规性，并证明它等价于"ε、φ 为最大弦长"；
- Laurent 多项式及其乘法、S₃ 作用、反对称化 J、轨道和、字符；
- 由半标准杨表定义的 Schur 多项式；
- Weyl 对称化。

主要结果：
- 主定理 `conjecture_00000003831_false : ¬ ClaimWeyl`；
- `weyl_forced`：B7 的任何 Weyl 对称化、任何 Schur 展开中，s₁₁₁ 的系数都是 −1；
- 轨道和、轨道平均、双交错系数以及抽象晶体等解释下的变体定理；
- 非平凡性：B(1,0,0) 与 B(2,1,0) 满足全部假设，且系数非负。

`verify.py` 用不同的方法独立复核上述全部内容，并执行 gl₂ 与 gl₃ 的极小性穷举搜索。
