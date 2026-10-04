# Counterexample to conjecture 00000001007

The conjecture says that in even characteristic every ovoid of the parabolic quadric
Q(4,q) is an elliptic quadric. **This is false for q = 8.** The counterexample is the
Suzuki–Tits ovoid (Tits 1962).

## The model

- **Field.** GF(8) = F₂[ω]/(ω³ + ω + 1). It has characteristic 2, and σ(x) = x⁴ satisfies σ² = Frobenius.
- **Quadric.** Q(4,8) is the zero set in PG(4,8) of Q(x) = x₀x₃ + x₁x₂ + x₄².
  - Its polar form is f(x,y) = x₀y₃ + x₃y₀ + x₁y₂ + x₂y₁.
  - The nucleus is N = (0,0,0,0,1).
- **The ovoid.** It consists of the 65 points
  `T = {(1, x, y, xy + x^6 + y^4, x^3 + y^2) : x, y ∈ GF(8)} ∪ {(0,0,0,1,0)}`.
  Here x^6 = x^{σ+2} and y^4 = y^σ. The last coordinate is the square root that lifts the
  Tits ovoid of PG(3,8) onto Q(4,8).

## Results

- **T is an ovoid of Q(4,8).** It has 65 = q²+1 points of the quadric and no two are
  collinear: f ≠ 0 on all 2080 pairs. Equivalently, it meets each of the 585 lines of
  Q(4,8) exactly once.
- **Reading R1 (inside PG(4,8)).** T lies in no hyperplane of PG(4,8). An elliptic quadric
  Q⁻(3,8) of Q(4,8) is a hyperplane section, so T is not one, even up to collineations.
- **Reading R2 (inside PG(3,8)).** The projection of T from N to PG(3,8) is the Tits ovoid,
  and it lies on no quadric. So T is not an elliptic quadric of PG(3,8), even up to
  collineations.
- **Hand proofs.** Both "no hyperplane" and "no quadric" have short proofs. A polynomial of
  degree ≤ 7 that vanishes on all of GF(8) is zero. Apply this to the points with x = 0 or
  y = 0.
- **Control.** E = Q(4,8) ∩ {x₄ = x₁ + x₂} is an elliptic-quadric ovoid. It satisfies every
  predicate used, so the predicates are not vacuous.
- **Parenthetical remark.** The statement says Suzuki's counterexamples are in odd
  characteristic. In fact they live only in characteristic 2, with q = 2^{2e+1} ≥ 8.
  We do not use the remark.

## Contents

- `report.tex`, `report.pdf`: the complete argument. This includes the proof that
  "q²+1 pairwise non-collinear points" is equivalent to "meets every line exactly once".
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent check in the Python 3 standard library. It builds GF(8) from
  discrete logarithms rather than from a multiplication table. It then checks:
  - by enumeration, every line of Q(4,8) and every hyperplane of PG(4,8);
  - no three points of the PG(3,8) Tits ovoid are collinear (all 43680 triples);
  - the 65 × 10 quadratic-monomial matrix has rank 10;
  - the control set E.
- `verification.txt`: the fresh build log, the forbidden-token scan and the Python output.

## Lean

- **The field.** `F8` is GF(8) with explicit tables. The field axioms, `char_two` and the
  order of ω are proved by `decide`.
- **The quadric.** `Q` and `pol` are the form and its polar form.
  - `Q_vadd` is the polarization identity, proved algebraically.
  - `Q_nondegenerate` shows that the radical is ⟨N⟩ and that Q(N) = 1.
- **The ovoid predicate.** `IsOvoid O` means:
  - O has 65 distinct, nonzero entries, all on Q;
  - `pol p q ≠ 0` for distinct entries p, q.

  `IsOvoid.at_most_one` proves that each totally singular line {s·u + t·v} contains at most
  one entry. `IsOvoid.proj_distinct` proves that the entries are distinct projective points.
- **The Tits ovoid.** `tits` is T, written with `sigma`. `tits_isOvoid` is proved by
  `decide +kernel`.
- **The two readings.** `InHyperplane` is the necessary condition of reading R1, and
  `OnQuadricPG3` (on a quadric after projection from N) is that of reading R2.
  - `tits_not_inHyperplane` and `tits_not_onQuadric` prove that T fails both.
  - The proofs use a general lemma: if c is orthogonal to the rows of E and N·E = I, then
    c = 0.
  - They also use explicit inverse-matrix certificates on 5 and 10 points of T.
- **Main theorems.**
  - `conjecture_00000001007_false : ¬ Conjecture1007_q8`, where
    `Conjecture1007_q8 := ∀ O, IsOvoid O → InHyperplane O`.
  - `conjecture_00000001007_false_any_reading`: let `IsElliptic` be any predicate whose
    instances satisfy `InHyperplane` or `OnQuadricPG3`. Then
    `¬ ∀ O, IsOvoid O → IsElliptic O`.
- **Non-vacuity.** `ell_isOvoid`, `ell_inHyperplane`, `ell_onQuadric` and `nonvacuous` show
  that the control ovoid E satisfies all the predicates.

The project has no `sorry`, no `native_decide` and no added axioms. `#print axioms` shows at
most `propext`, `Classical.choice` and `Quot.sound`.

**Limitations.** Lean treats q = 8 in the standard model of Q(4,8); this is enough because the
conjecture covers every even q. Lean proves the "at most one point per line" half of the
equivalence with the line definition of an ovoid. The counting half is in the report, and
`verify.py` checks it exhaustively on all 585 lines. "Elliptic quadric" enters Lean only
through its necessary conditions, which makes the disproof stronger.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想声称：在偶特征下，抛物二次曲面 Q(4,q) 的每个 ovoid 都是椭圆二次曲面。这在 q = 8 时不成立。

- **反例。** 取 GF(8) = F₂[ω]/(ω³+ω+1)，σ(x) = x⁴（σ² 为 Frobenius）。把 Suzuki–Tits ovoid（Tits 1962）
  提升到 Q(4,8)：x₀x₃ + x₁x₂ + x₄² = 0。得到 65 个点
  (1, x, y, xy + x⁶ + y⁴, x³ + y²) 与 (0,0,0,1,0)。
- **它是 ovoid。** 这 65 = q²+1 个点两两不共线（极化形式 f ≠ 0），等价地与 Q(4,8) 的 585 条直线
  各恰交于一点。
- **它不是椭圆二次曲面。** 它不含于 PG(4,8) 的任何超平面，因此不是超平面截口 Q⁻(3,8)。从核
  (0,0,0,0,1) 投影到 PG(3,8) 后，它不在任何二次曲面上，因此在 PG(3,8) 模型中也不是椭圆二次曲面。
  两个结论都有简短的手工证明：次数 ≤ 7 且在 GF(8) 上处处为零的多项式恒为零。
- **非空性。** 对照例 E = Q(4,8) ∩ {x₄ = x₁+x₂} 满足所有谓词，说明谓词不是空的。
- **Lean。** Lean 4.19（仅核心库）定义了：
  - 域 GF(8)，并穷举验证域公理；
  - 二次型 Q 及其非退化性；
  - ovoid 谓词 IsOvoid，并证明它与每条全奇异直线至多交于一点；
  - 两种读法下的必要条件：在某超平面内，或投影后在某二次曲面上。

  Lean 证明了猜想的否定 `conjecture_00000001007_false`，以及对任意读法都成立的版本。
- **独立验证。** `verify.py` 只用 Python 标准库，穷举检查了全部直线、全部超平面和二次单项式矩阵的秩。
- **关于括号注记。** 原题说 Suzuki 反例出现在奇特征，这是错的：它们只存在于特征 2。本证明不依赖这条注记。
