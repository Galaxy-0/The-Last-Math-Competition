# Disproof of conjecture 00000007608

The conjecture says: "The composition of two reflections is a rotation and the decomposition is
unique; the exception of uniqueness is parallel reflections; and the exception of parallel
reflections is translation composition."

We refute the **uniqueness clause**: "the decomposition of a rotation into two reflections is
unique, and the exception is parallel mirrors". The conjecture is a conjunction, so this
refutes it.

## The counterexample

- **The general theorem.** Let `R_α` be the reflection in the line through the centre at angle
  `α`, and `ρ_θ` the rotation by `θ`. Then `R_β ∘ R_α = ρ_θ` whenever `β − α ≡ θ/2 (mod π)`.
  So for **every** rotation `ρ ≠ id`:
  - the decompositions are exactly the pairs `(A, ρA)`, where `A` is an arbitrary reflection;
  - there is a circle's worth of them (`α ∈ ℝ/πℤ`);
  - none of them has parallel mirrors.

  Uniqueness fails for every nontrivial rotation. The named exception, parallel mirrors, never
  occurs for `ρ ≠ id`: equal mirrors through the centre give `B = A` and `BA = id`.
- **The simplest instance (90°).** Let
  - `R1 = diag(1,−1)`, mirror the x-axis;
  - `R2 = [[0,1],[1,0]]`, mirror the line y = x;
  - `R3 = diag(−1,1)`, mirror the y-axis;
  - `R4 = [[0,−1],[−1,0]]`, mirror the line y = −x.

  Then `R2·R1 = R4·R3 = [[0,−1],[1,0]]`, and the four mirrors are pairwise different.
- **The 180° rotation.** `R3·R1 = R4·R2 = R2·R4 = −I`.
- **An infinite rational family.** `A_t = [[1−t², 2t],[2t, t²−1]]/(1+t²)` with `t ∈ ℕ`. Its
  mirror is the line of slope `t`. For every rational rotation `ρ ≠ I`, the pairs
  `(A_t, ρA_t)` are:
  - non-parallel decompositions of `ρ`;
  - pairwise different, with different first mirrors;
  - such that no three share an unordered mirror pair.

The following readings are covered:

- **Ordered and unordered pairs.** Lean refutes the weakest form, which compares unordered
  pairs of mirrors as lines. This also refutes the ordered, matrix-level form.
- **Every rotation `≠ id`.** The identity is the only rotation for which the clause holds
  (vacuously).
- **ℝ and ℚ.** The report proves the result over ℝ; Lean proves it over ℚ.
- **ℝ³ / ℝⁿ.** For hyperplane mirrors, the mirror pairs are the hyperplanes containing the
  rotation axis. Lean includes a block-diagonal example in ℝ³.
- **Affine reflections.** A rotation about `c` has its mirrors through `c`, which gives the same
  family. Lean shows the 90° rotation about `(1,1)` as `S(y=x)∘S(y=1) = S(x+y=2)∘S(x=1)`.

**Literal-reading convention.** The disproof relies on the literal reading of the bilingual
text: "分解唯一；且唯一性的例外为平行反射" (the decomposition is unique, and the exception to
uniqueness is parallel reflections). Clauses 1 and 4 are correct (see below), so the
conjunction fails through the uniqueness clause.

**Charitable reading 1: "unique up to rotating both mirrors simultaneously".** Only the angle
between the mirrors is determined. This weakened statement is true, and we do not refute it.
Standard texts, however, state the *non*-uniqueness: one of the two mirrors through the centre
may be chosen arbitrarily (Coxeter, *Introduction to Geometry*, Ch. 3; Brannan–Esplen–Gray,
*Geometry*). This supports reading "unique" literally.

**Charitable reading 2: relative uniqueness.** "Given one mirror, the other is unique." This is
also true; Lean proves it as `decomp_classification` (`BA = ρ ⇒ B = ρA`). It is not what is
stated. It holds for translations too, so under this reading the stated exception (parallel
mirrors) would be vacuous.

**Clauses 1 and 4.** For linear reflections, clause 1 ("the composition is a rotation") is true
(`refl_mul_refl`). For affine reflections with parallel distinct mirrors, the composition is a
fixed-point-free translation, so clause 1 fails there. Clause 4 names exactly this exception.
Clauses 1 and 4 are therefore correct, and the disproof does not use them.

## Contents

- `report.tex`, `report.pdf`: the complete proof, both the real and the rational versions, and
  the discussion of readings.
- `lean4/`: a Lean 4.19.0 project, core library only.
- `verify.py`: an independent check in Python 3 using only the standard library. It uses exact
  `Fraction` matrices, computes mirrors by Gaussian elimination, checks the symbolic identities
  with polynomial arithmetic, and uses brute force:
  - for 123 rational rotations × 86 parameters `t`, every pair is a non-parallel decomposition;
  - inside a set of 124 rational reflections it enumerates all decompositions (124 for 90°);
  - it checks the ℝ³ and affine cases;
  - it gives a floating-point illustration for irrational angles.
- `verification.txt`: the fresh `lake build` log with the axiom report, the forbidden-token
  scan and the output of `verify.py`.

## Lean

Everything is defined from scratch:

- integer matrices `M2`;
- rational matrices `QM = m/q`, with equality `QEq` (an equivalence relation);
- `IsRefl`: orthogonal, det −1 and an involution;
- `IsRot`: orthogonal with det +1;
- `Fix` and the mirror;
- `SameMirror`: parallel, which means equal for mirrors through the origin;
- `Decomp ρ A B`: `A` and `B` are reflections and `B·A = ρ`.

Main theorems:

- **`conjecture_00000007608_false : ¬ UniqueClause`**, where
  `UniqueClause := ∀ ρ, IsRot ρ → ∀ A B A' B', Decomp ρ A B → Decomp ρ A' B' → ¬SameMirror A B → ¬SameMirror A' B' → SameMirrorPair A B A' B'`
  (same unordered pair of mirrors).
- `conjecture_false_ordered`: the ordered, matrix-level reading.
- `conjecture_false_rot90_explicit`: the claim fails directly from `R2·R1 = R4·R3`.
- `every_nontrivial_rotation_fails : ∀ ρ, IsRot ρ → ¬QEq ρ Id2 → ¬UniqueFor ρ`.
- `infinitely_many_decompositions`, `decomp_classification` (every decomposition is
  `(A, ρA)`), `decomp_of_refl`, `rot_mul_refl`, `refl_mul_refl` and `isRefl_iff`.
- Non-vacuity:
  - `uniqueFor_id`: for `ρ = id` the predicate holds;
  - `rot90_two_decompositions` and `rot180_two_decompositions`;
  - `Aref2_example`: `A_2 = [[-3,4],[4,3]]/5`.
- `r3_two_decompositions` (ℝ³), and `parallel_gives_translation` and
  `affine_two_decompositions` (affine).

The project has no `sorry` and no `native_decide`. The only axioms are `propext` and
`Quot.sound`. Core Lean has no `ring`, so a small tactic `ring_z` (expand, AC-normalise, then
`omega`) proves the polynomial identities.

Limitations:

- Lean works over ℚ, and the real statement is proved in the report.
- The ℝ³ and affine parts are concrete examples.
- The general ℝⁿ and affine reductions, and the "up to rotation" statement, are proved in the
  report only.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想："两反射的合成为旋转且分解唯一；且唯一性的例外为平行反射；且平行反射的例外为平移复合。"
我们否定其中的唯一性部分，即"旋转分解为两个反射的方式唯一，唯一的例外是镜面平行"。猜想是合取命题，所以猜想不成立。

**一般定理。** 记 `R_α` 为关于过中心、倾角为 `α` 的直线的反射，`ρ_θ` 为转角 `θ` 的旋转。只要 `β − α ≡ θ/2 (mod π)`，就有 `R_β ∘ R_α = ρ_θ`。因此对**每一个**非恒等旋转 `ρ`：
- 它的全部分解恰为 `(A, ρA)`，其中 `A` 为任意反射；
- 这样的分解有一整个圆周那么多；
- 其中没有任何一个的两镜面平行。

所以唯一性对所有非平凡旋转都不成立。而猜想所说的例外（镜面平行）在 `ρ ≠ id` 时根本不会出现：过中心的两条平行镜面必相同，这时 `B = A`，`BA = id`。

**最简单的例子（90°）。**
- `R1 = diag(1,−1)`，镜面为 x 轴；
- `R2 = [[0,1],[1,0]]`，镜面为 y = x；
- `R3 = diag(−1,1)`，镜面为 y 轴；
- `R4 = [[0,−1],[−1,0]]`，镜面为 y = −x。

则 `R2·R1 = R4·R3 = [[0,−1],[1,0]]`，四条镜面两两不同。180° 的情形：`R3·R1 = R4·R2 = −I`。

**有理数无穷族。** `A_t = [[1−t², 2t],[2t, t²−1]]/(1+t²)`（`t ∈ ℕ`），其镜面是斜率为 `t` 的直线。对每个有理旋转 `ρ ≠ I`，`(A_t, ρA_t)` 都是 `ρ` 的分解，且：
- 两镜面不平行；
- 不同的 `t` 给出不同的第一镜面；
- 任意三个分解的无序镜面对不全相同。

**覆盖的读法：**
- 有序对与无序对都覆盖（Lean 否定的是最弱的"无序镜面对唯一"）；
- 覆盖所有非恒等旋转；
- 实数情形（报告）与有理数情形（Lean）；
- ℝ³ 及一般 ℝⁿ 中的超平面镜面（Lean 给出分块嵌入的例子）；
- 仿射反射：绕点 c 的旋转，其两镜面必过 c，于是有同样的无穷族。

**字面读法约定。** 本否定依据中英文原文的字面含义："分解唯一；且唯一性的例外为平行反射"。第一条和第四条是正确的（见下），所以合取命题是因唯一性部分而不成立。

**宽容读法一："在两镜面同时旋转的意义下唯一"。** 只有两镜面的夹角是确定的。这个弱化命题是正确的，本文不否定它。但标准教材讲的恰恰是**不**唯一性：过中心的两个镜面中，可以任意选定其中一个（Coxeter《Introduction to Geometry》第 3 章；Brannan–Esplen–Gray《Geometry》）。这支持按字面理解"唯一"。

**宽容读法二：相对唯一性。** "给定一个镜面，另一个唯一"。这也是正确的，Lean 中即 `decomp_classification`（`BA = ρ ⇒ B = ρA`）。但这不是原文所说的。而且平移也满足相对唯一性，所以在这种读法下，原文所说的例外（平行镜面）就没有意义了。

**关于第一条和第四条。** 对线性反射，第一条"合成为旋转"成立（`refl_mul_refl`）。对仿射反射，两镜面平行且不同时，合成是无不动点的平移，第一条在此不成立，这正是第四条所说的例外。因此第一条和第四条正确，本否定不依赖它们。

**Lean 4.19.0（仅核心库）。** 从零定义了以下对象：
- 有理 2×2 矩阵 `m/q`；
- 反射：正交、行列式 −1、对合；
- 旋转：正交、行列式 +1；
- 镜面（不动直线）、平行（镜面相等），以及分解。

主定理 `conjecture_00000007608_false : ¬ UniqueClause`；另有：
- `every_nontrivial_rotation_fails`、`infinitely_many_decompositions`；
- `decomp_classification`：每个分解都是 `(A, ρA)`。

不使用 sorry 或 native_decide，只用到公理 propext 和 Quot.sound。
`verify.py` 只用 Python 标准库，以精确有理数矩阵、高斯消元求镜面、多项式恒等式检验和穷举，独立复核以上全部结论。
