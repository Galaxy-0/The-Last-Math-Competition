# Disproof of conjecture 00000004310

**Claim.** There exist two imaginary quadratic fields of the same discriminant whose class
groups have isomorphic 3-parts while their unit groups are not isomorphic, and the smallest such
discriminant has seven digits.

**Verdict: false.** No such pair exists, whatever the class-group condition means. So there is no
witness discriminant, and in particular no smallest one with seven digits.

## Why

1. **The discriminant determines the field.**
   - Every imaginary quadratic field is `Q(√m)` for a unique squarefree `m < 0` (Marcus,
     *Number Fields*, Ch. 2).
   - Its discriminant is `D = m` if `m ≡ 1 (mod 4)`, and `D = 4m` otherwise.
   - The map `m ↦ D` is injective: `4m ≡ 0 (mod 4)` can never equal some `m' ≡ 1 (mod 4)`, and
     `4m = 4m'` gives `m = m'`.
   - So two fields with the same discriminant are the same field (isomorphic, or equal inside
     `C`), and their unit groups are isomorphic.
2. **The unit group depends only on `D` (a second, independent argument).**
   - The ring of integers is `Z[ω]` with `ω² = tω − n`, where `t = D mod 2` and
     `n = (t − D)/4`.
   - Its norm form satisfies `4N(a + bω) = (2a + tb)² + |D| b²`.
   - So the units are `±1`, except `μ_4 = {±1, ±i}` for `D = −4` and `μ_6` for `D = −3`.
   - The unit group is cyclic of order `w(D) ∈ {4, 6, 2}`, a function of `D`.

## Readings covered

| reading | result |
|---|---|
| fields as subfields of `C` / up to isomorphism | `K1 = K2` / `K1 ≅ K2`, so the unit groups are isomorphic |
| "two" fields must be distinct | there are no two distinct fields with the same `D` |
| any meaning of "3-part of the class group" | irrelevant: Lean treats it as an arbitrary predicate `C3` |
| imaginary quadratic **orders** of discriminant `D` | there is one order per `D`, with unit group `Z/w(D)` (proved in Lean for every `D`) |
| binary quadratic **forms** of discriminant `D` | every form has `w(D)` automorphs, and the class group `C(D)` depends only on `D` (report, `verify.py`) |
| `|D|` instead of `D` | both discriminants are negative, so this is the same as equal `D` |
| "same discriminant" dropped | witnesses exist but are tiny: `Q(√−3)`, `Q(i)`, `Q(√−2)` have `h = 1` and `w = 6, 4, 2`, with `D = −3, −4, −8`; one digit, not seven |
| two **real** quadratic fields with the same `D` | same field (the `disc` formula and its injectivity are unchanged), and every real unit group is `≅ Z/2 × Z` anyway |
| a real and an imaginary field with the same `|D|` | witnesses exist but are tiny: `Q(√2)`, `Q(√−2)`, `|D| = 8`, both `h = 1`, units `Z/2 × Z` vs `Z/2`; one digit, not seven |

**About "seven digits".** This possibly echoes the classical computations (Diaz y Diaz, 1974) of
imaginary quadratic fields whose class group has 3-rank 3, where the smallest discriminants have
seven digits. That is a statement about class groups alone. Any separation of unit groups
between imaginary fields forces `Q(i)` or `Q(√−3)` into the pair. Real/real separation is
impossible, and real/imaginary already occurs at `|D| = 8`. So no repair that keeps the
unit-group condition yields a seven-digit minimum.

## Contents

- `report.tex`, `report.pdf`: the complete proof, the background facts with references, and the
  readings.
- `lean4/`: a Lean 4.19.0 project, core library only (no Mathlib). It builds in about 10 seconds.
- `verify.py`: an independent Python 3 standard-library check. It verifies:
  - injectivity of `disc` on all 12160 squarefree `−20000 < m < 0`, and that its values are
    exactly the fundamental discriminants;
  - brute-force unit counts for these fields;
  - unit groups of all orders with `−10^4 < D < 0` (`t² − Du² = 4`), and that they are cyclic;
  - automorphs of all 143695 reduced primitive forms with `|D| < 10^4` (brute force over
    `SL_2` for `|D| < 400`);
  - class numbers for the weakened reading.
- `verification.txt`: a fresh `lake build` log with `#print axioms`, the forbidden-token scan,
  and the output of `verify.py`.

## Lean

Everything is defined from scratch:

- `Squarefree`, `IsImagQuadParam`, `disc`.
- `QR` with `mul t n`, the ring `Z[ω]` of pairs, with proved ring laws, `norm`, `trace`, `conj`
  and `discBasis`.
- `fT m`, `fN m`: the ring of integers `O_m`.
- `tD D`, `nD D`: the order of discriminant `D`.
- `IsUnitQ` and `UnitGrp` for units, and `MulIso` for isomorphisms.

Key theorems:

```lean
theorem disc_injective {m₁ m₂ : Int} (h : disc m₁ = disc m₂) : m₁ = m₂
theorem integral_iff {m : Int} (hm : m % 4 ≠ 0) (x y : Int) :
    (∃ q, halfCoords m q = (x, y)) ↔ (4 : Int) ∣ x * x - m * (y * y)   -- the O_K formula
theorem field_discBasis (m : Int) : discBasis (fT m) (fN m) = disc m
theorem units_classification {D : Int} (hD : ValidDisc D) (x : QR) :
    IsUnitQ (tD D) (nD D) x ↔ x ∈ unitList D        -- ±1; ±1,±i; μ₆
theorem unitList_eq_pows {D : Int} (hD : ValidDisc D) :
    (List.range (w D)).map (pow (tD D) (nD D) (gen D)) = unitList D ∧
      pow (tD D) (nD D) (gen D) (w D) = one          -- cyclic of order w D
theorem field_units_pm_one {m : Int} (hm : IsImagQuadParam m) (h1 : m ≠ -1) (h3 : m ≠ -3)
    (x : QR) : IsUnitQ (fT m) (fN m) x ↔ x = ⟨1, 0⟩ ∨ x = ⟨-1, 0⟩
theorem orderUnits_iso_of_w_eq {D₁ D₂ : Int} (h₁ : ValidDisc D₁) (h₂ : ValidDisc D₂)
    (hw : w D₁ = w D₂) : Nonempty (MulIso (OrderUnits D₁) (OrderUnits D₂))

def Claim (C3 : Int → Int → Prop) : Prop :=
  ∃ m₁ m₂ : Int, IsImagQuadParam m₁ ∧ IsImagQuadParam m₂ ∧ disc m₁ = disc m₂ ∧ C3 m₁ m₂ ∧
    ¬ Nonempty (MulIso (FieldUnits m₁) (FieldUnits m₂))
theorem conjecture_00000004310_false (C3 : Int → Int → Prop) : ¬ Claim C3   -- via injectivity
theorem conjecture_00000004310_false' (C3 : Int → Int → Prop) : ¬ Claim C3  -- via w(D) only
theorem smallest_seven_digit_false (C3 : Int → Int → Prop) :
    ¬ ∃ D : Int, 1000000 ≤ D.natAbs ∧ D.natAbs < 10000000 ∧ Witness C3 D ∧
      ∀ D', Witness C3 D' → D.natAbs ≤ D'.natAbs
theorem order_claim_false (C3 : Int → Int → Prop) : ¬ OrderClaim C3
theorem fieldUnits_not_iso : ¬ Nonempty (MulIso (FieldUnits (-1)) (FieldUnits (-2)))  -- non-vacuity
```

Axioms used: `propext`, `Quot.sound` and `Classical.choice`. There is no `sorry` and no
`native_decide`.

**Limitations.**

- Once fields are parametrised by `m`, the first proof `conjecture_00000004310_false` is
  immediate: it is just `disc_injective`. The mathematical content of the disproof is the cited
  classification (F1)–(F4) plus the `w(D)` argument, formalized in `units_classification`,
  `unitList_eq_pows`, `orderUnits_iso_of_w_eq` and the second proof
  `conjecture_00000004310_false'`.
- The real-quadratic readings are argued in the report and checked in `verify.py`, not in Lean.

- Lean does not construct `Q(√m)` itself. The bridge "imaginary quadratic field ↔ squarefree
  `m < 0` with ring `O_m`" is the textbook classification (F1)–(F4) in the report.
- Lean does prove the integer core of the `O_K` formula (`integral_iff`, `halfCoords_mul`) and
  the discriminant as the determinant of the trace form.
- Class groups are not formalized. They appear only as an arbitrary predicate, which is enough
  because the refuted existential fails for every value of that predicate.

No previous submission exists for this conjecture.

## 中文说明

**猜想**：存在两个判别式相同的虚二次域，其类群的 3 部分同构，而单位群不同构；并且这样的最小判别式是一个七位数。

**结论：猜想不成立。** 无论类群条件如何理解，这样的两个域都不存在。因此根本没有满足条件的判别式，更谈不上"最小判别式为七位数"。

**理由一：判别式决定域。**

- 每个虚二次域都是 `Q(√m)`，其中 `m < 0` 是唯一确定的无平方因子整数。
- 其判别式为：`m ≡ 1 (mod 4)` 时 `D = m`，否则 `D = 4m`。
- 映射 `m ↦ D` 是单射：`4m ≡ 0 (mod 4)` 不可能等于某个 `m' ≡ 1 (mod 4)`，而 `4m = 4m'` 推出 `m = m'`。
- 所以判别式相同的两个虚二次域是同一个域，单位群自然同构。

**理由二（不依赖单射性）：单位群只依赖于判别式。**

- 整数环为 `Z[ω]`，其中 `ω² = tω − n`，`t = D mod 2`，`n = (t − D)/4`。
- 范数满足 `4N(a + bω) = (2a + tb)² + |D| b²`。
- 因此 `D = −4` 时单位群为 `μ_4`，`D = −3` 时为 `μ_6`，其余情形为 `{±1}`。
- 单位群总是阶为 `w(D)` 的循环群，只由 `D` 决定。

**各种读法**：

- 把"两个域"理解为 `C` 的子域或同构类，结论都相同。
- 若要求两个域不同，则根本不存在判别式相同的两个不同的域。
- 类群条件在 Lean 中作为任意谓词处理，不影响结论。
- 理解为虚二次序（order）时，每个判别式只有一个序，其单位群为 `Z/w(D)`。
- 理解为二元二次型时，判别式为 `D` 的每个型都恰有 `w(D)` 个自同构，型类群也只依赖于 `D`。
- 若去掉"同判别式"，确实存在满足条件的例子，但判别式极小：`Q(√−3)`、`Q(i)`、`Q(√−2)` 的类数都是 1，单位群阶分别为 6、4、2，判别式为 −3、−4、−8，都是一位数而非七位数。
- 两个判别式相同的**实**二次域也必是同一个域（判别式公式及其单射性不变）；况且每个实二次域的单位群都同构于 `Z/2 × Z`。
- 一个实二次域与一个虚二次域、判别式绝对值相同时，确有满足条件的例子，但判别式极小：`Q(√2)` 与 `Q(√−2)`，`|D| = 8`，类数都是 1，单位群分别为 `Z/2 × Z` 与 `Z/2`。这是一位数，不是七位数。

**关于"七位数"**：这或许来自 Diaz y Diaz（1974）关于类群 3-秩为 3 的虚二次域的计算，其中最小判别式是七位数量级。但那只涉及类群。只要保留"单位群不同构"这一条件：虚二次域之间的分离必然涉及 `Q(i)` 或 `Q(√−3)`；实二次域之间不可能分离；实、虚混合在 `|D| = 8` 就已出现。所以任何保留单位群条件的修正都不会得到七位数的最小判别式。

**说明**：一旦用 `m` 参数化虚二次域，第一个 Lean 证明 `conjecture_00000004310_false` 就只是判别式单射性的直接推论。真正的数学内容是所引用的经典分类 (F1)–(F4)，加上 `w(D)` 论证（`units_classification`、`unitList_eq_pows` 与第二个证明 `conjecture_00000004310_false'`）。实二次域的读法只在报告和 `verify.py` 中处理，没有在 Lean 中形式化。

**Lean 形式化**：只用 Lean 4.19.0 核心库，所有对象从零定义，包括无平方因子、判别式、整数对表示的二次环（证明了环公理）、整数环 `O_m`、任意判别式的序、单位群和群同构。主要定理：

- `disc_injective`：判别式是单射。
- `integral_iff`：`O_K` 公式的整数部分。
- `units_classification` 与 `unitList_eq_pows`：单位群的完全分类，以及它是 `w(D)` 阶循环群。
- `conjecture_00000004310_false`：`¬ Claim C3`，对任意类群谓词 `C3` 成立。
- `smallest_seven_digit_false`：否定"最小判别式为七位数"。
- `order_claim_false`：否定"序"的读法。
- `fieldUnits_not_iso`：说明"单位群不同构"这一条件本身并非空洞。

**独立验证**：`verify.py` 只用 Python 标准库，用不同方法进行检验：

- 对 `|m| < 20000` 检验判别式的单射性和单位群；
- 对 `|D| < 10^4` 检验所有序的单位群；
- 对 `|D| < 10^4` 检验所有约化本原二次型的自同构群。
