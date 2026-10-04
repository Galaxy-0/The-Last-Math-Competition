# Disproof of conjecture 00000001753

The conjecture says that every spin character χ of the double cover 2·S_n satisfies
**|χ(g)| ≤ 2^{⌊n/4⌋−1}** for every g in an "alternating class", i.e. every g lying over an
even permutation.

**This is false.** At n = 5 the bound is 2^{1−1} = 1. The basic spin character χ of 2·S_5
has degree 4 and is irreducible. At g = t₁t₂, which lies over the 3-cycle (1 2 3), it takes
the value χ(g) = −2. So |χ(g)| = 2 > 1. The same happens for both double covers of S_5, and
by Schur's formula for every n ≥ 5.

## The counterexample

1. **The double covers.** Schur's presentations use generators t₁,…,t₄ and a central z with
   z² = 1:
   - Ŝ₅: t_i² = 1, (t_i t_{i+1})³ = 1, (t_i t_j)² = z for |i−j| ≥ 2;
   - S̃₅: t_i² = z, (t_i t_{i+1})³ = z, (t_i t_j)² = z for |i−j| ≥ 2.

   A spin representation is a list of matrices satisfying these relations with z ↦ −I
   (von Dyck).
2. **The basic spin representation.** Take ξ₁,…,ξ₅, five anticommuting involutions in
   M₄(ℂ), and set T_i = (ξ_i − ξ_{i+1})/√2. Clifford algebra identities give the Ŝ₅
   relations. The matrices iT_i give the S̃₅ relations.
3. **Irreducibility.** The T_i generate the Clifford algebra of a 4-dimensional space, which
   is all of M₄(ℂ). So the representation is irreducible. Also ⟨χ,χ⟩ = 1 and
   χ(z) = −4 = −χ(1), so χ is an irreducible spin character.
4. **The value.** T₁T₂ = ½(ξ₁ξ₂ − ξ₁ξ₃ − I + ξ₂ξ₃), and tr(ξ_aξ_b) = 0 for a ≠ b. So
   χ(t₁t₂) = −2 for Ŝ₅, and +2 for S̃₅. Since t₁t₂ lies over (1 2 3), which is even and not
   the identity, the bound 1 fails.

**All n.** By Schur's formula (Schur 1911; Stembridge 1989; Hoffman–Humphreys 1992) the basic
spin character has absolute value 2^{⌊(n−3)/2⌋} on a lifted 3-cycle. This exceeds
2^{⌊n/4⌋−1} for every n ≥ 5. For n = 4 the identity (degree 2 > 1) violates the bound.

## Readings covered

- **Which cover.** Both double covers Ŝ₅ and S̃₅ are refuted, in Lean as well.
- **Alternating classes.** These are classes of 2·S_n over A_n, or classes of 2·A_n. Our g
  lies in 2·A₅ under either reading, and it is not the identity.
- **"For large n".** The claim fails for every n ≥ 5.
- **Reducible spin characters.** Our χ is irreducible, so it is a spin character either way.
- **Characters of 2·A₅.** The claim still fails: on a lifted 5-cycle the degree-2 spin
  characters of 2·A₅ ≅ SL(2,5) take the value (1+√5)/2 > 1 (`verify.py`).
- **"Alternating" read as odd classes.** The claim still fails at n = 4: |χ±(lifted
  4-cycle)| = √2 > 1 (`verify.py`, exact). At n = 5 Schur's formula gives √2 for the (4,1)
  pair (cited).
- **⟨χ,g⟩ as an inner product.** If ⟨χ,g⟩ meant the inner product ⟨χ, 1_C⟩ with the class
  indicator, the statement would be trivially true by column orthogonality. We consider this
  reading unintended and make no claim under it (see the report).

## Contents

- `report.tex`, `report.pdf`: the complete argument.
- `lean4/`: a Lean 4.19.0 project, core library only. It builds in about 40 s.
- `verify.py`: an independent check using the Python 3 standard library (a few seconds).
- `verification.txt`: the build log, axiom audit and Python output.

## Lean

**Definitions**

- `Z8`: the ring ℤ[ζ], ζ = e^{πi/4}, with conjugation and `normSq`.
- Matrices as lists of rows, `eval` of a word, and `wordPerm`, the projection to S_n.
- `IsSpinRep c n d T`: Schur's relations for the cover `c` (`hat`/`tilde`) with z ↦ −I.
- `SpansMatrices d T`: the words span M_d. This gives irreducibility.
- `Claim c n`: for all irreducible spin representations over ℤ[ζ], every word over an even
  permutation has |χ|² ≤ 4^{⌊n/4⌋−1} whenever |χ|² is an integer. This is a weakening of the
  conjecture, so refuting it refutes the conjecture.

**Main theorem**

- `conjecture_00000001753_false (c : Cover) : ¬ Claim c 5`, and
  `conjecture_00000001753_false_both`.

**Ingredients**

- `spinRep c`: the relations hold for both covers.
- `spans c`: an explicit certificate writes 5·E_ab as a ℤ[ζ]-combination of 16 words.
- `t1t2_perm` and `t1t2_even`: t₁t₂ lies over the 3-cycle, which is even.
- `normSq_t1t2`: |χ(t₁t₂)|² = 4.
- `chi_z`: χ(z) = −4.
- `perm_relations`: the projection to S₅ is well defined.
- `z_ne_one` and `perm_words_distinct`: the presented group has at least 240 elements.

**Axioms.** There is no `sorry`, no `native_decide` and no added axiom. Every printed theorem
depends on no axioms at all.

**Cited, not formalized**

- Schur's theorem that the presented groups have order exactly 240, i.e. are the double
  covers. `verify.py` enumerates the image group of the Lean matrices: 240 elements, with
  kernel {±I} over S₅.
- Schur's character formula for general n.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想：2·S_n 的每个自旋特征标 χ 在交错类上（即位于偶置换之上的元素 g）满足 |χ(g)| ≤ 2^{⌊n/4⌋−1}。

**结论：猜想不成立。** 取 n = 5，此时上界为 2^{1−1} = 1。2·S_5 的基本自旋特征标 χ 次数为 4，且不可约。
元素 g = t₁t₂ 位于 3-轮换 (1 2 3)（偶置换，且不是单位元）之上，而 χ(g) = −2，所以 |χ(g)| = 2 > 1。

**构造：**
- 取 5 个两两反交换的对合矩阵 ξ₁,…,ξ₅ ∈ M₄(ℂ)，令 T_i = (ξ_i − ξ_{i+1})/√2。
- 由 Clifford 代数恒等式，T_i 满足 Schur 表现 Ŝ₅ 的关系（t_i² = 1，(t_i t_{i+1})³ = 1，|i−j| ≥ 2 时 (t_i t_j)² = z），且 z ↦ −I。
- iT_i 满足另一个双覆盖 S̃₅ 的关系（t_i² = z）。
- T_i 生成整个 M₄(ℂ)，因此表示不可约；又 χ(z) = −4 = −χ(1)，所以 χ 是不可约自旋特征标。
- 由 tr(ξ_aξ_b) = 0（a ≠ b）得 χ(t₁t₂) = −2（对 S̃₅ 为 +2）。

**一般 n：** 由 Schur 公式，基本自旋特征标在 3-轮换的提升上的绝对值为 2^{⌊(n−3)/2⌋}，对所有 n ≥ 5 都大于 2^{⌊n/4⌋−1}。
n = 4 时，单位元（次数 2 > 1）已违反上界。

**其他读法：**
- 两个双覆盖都被否定。
- g 属于 2·A₅，因此按"2·S_n 中位于 A_n 之上的类"或"2·A_n 的类"两种读法都成立。
- "对充分大的 n"的读法同样不成立（所有 n ≥ 5 均为反例）。
- 若指 2·A₅ 的特征标，二维自旋特征标在 5-轮换提升上的值为 (1+√5)/2 > 1。
- 若"交错类"指奇类，n = 4 时值的绝对值为 √2 > 1。
- 若把 ⟨χ,g⟩ 理解为与类指示函数的内积，命题平凡成立；我们认为这不是本意，对此不作断言。

**Lean 部分**（仅用核心库）：
- 在 ℤ[ζ₈] 上定义矩阵、Schur 关系（自旋表示）、不可约性（单词张成全矩阵代数）以及到 S_n 的投影。
- 主定理为 `conjecture_00000001753_false (c) : ¬ Claim c 5`，对两个双覆盖都成立。
- 不可约性由显式证书验证：5·E_ab 是 16 个单词的 ℤ[ζ]-线性组合。
- 没有 sorry、native_decide 或额外公理。
- 引用而未形式化的结果：表现群的阶恰为 240（Schur 定理），以及一般 n 的 Schur 特征标公式。

**verify.py**（仅用标准库）：
- 精确验证 Lean 中矩阵的关系；
- 枚举 240 阶群，验证核为 {±I}、⟨χ,χ⟩ = 1；
- 用 Clifford 模型对 n = 4,5,6,7 验证群阶 2·n! 与 Schur 公式；
- 检查其他读法。
