# Counterexample to conjecture 00000007130

The conjecture says that the period of the Ehrhart quasi-polynomial is the least common
multiple of the denominators. The statement is a conjunction, and we refute this clause. It is
false because of *period collapse* (McAllister–Woods, JCTA 2005):

```
T = conv{(0,0), (1,1/2), (2,0)}      vertex denominators: lcm = 2
#(tT ∩ ℤ²) = (t+1)(t+2)/2            for every t ≥ 0   (1, 3, 6, 10, 15, 21, ...)
```

So the Ehrhart quasi-polynomial of `T` is a polynomial, and its (minimal) period is `1 ≠ 2`.

Proof: an integer point `(x,y)` lies in `tT` exactly when `y ≥ 0`, `2y ≤ x` and `x + 2y ≤ 2t`
(these are the unique barycentric weights `2y`, `(x−2y)/2`, `(2t−x−2y)/2`). Row `y` therefore has
`2t+1−4y` points for `4y ≤ 2t` and none otherwise. Summing gives `(m+1)(2m+1)` for `t = 2m` and
`(m+1)(2m+3)` for `t = 2m+1`, both equal to `(t+1)(t+2)/2`.

Readings:
- **"The period"** means the minimal period. The lcm `2` is still *a* period of `L_T`, as
  Ehrhart's theorem says. Under the reading "the lcm is a period" with vertex denominators the
  clause is a true theorem, and we say so.
- **Facet denominators.** Here the denominators are those of the right-hand sides `b` in
  `a·x ≤ b` with primitive integer normals `a`, i.e. the least `d` such that every facet
  hyperplane of `dP` contains a lattice point. `T` does not refute this reading: its facets
  `−y ≤ 0`, `−x+2y ≤ 0`, `x+2y ≤ 2` give lcm `1`, which equals the period. The control triangle
  `T₂ = conv{(0,0),(1,0),(0,1/2)}` does refute it. Its facets are `x ≥ 0`, `y ≥ 0`, `x+2y ≤ 1`
  (lcm `1`), but `4·#(tT₂ ∩ ℤ²) + (t mod 2) = (t+2)²`, so its period is exactly `2`. Since `1` is
  not even *a* period, this refutes the weak form as well.
- **Coefficient denominators.** The Ehrhart polynomial `t²/2 + 3t/2 + 1` of `T` has coefficient lcm
  `2 ≠ 1`, so this reading fails for `T` too.
- **"Lattice polytopes".** With vertex or facet denominators, the lattice-only reading is trivially
  true ("1 = 1"). The words quasi-polynomial, period and denominators only make sense for rational
  polytopes, so we use the rational reading. With coefficient denominators the lattice reading fails
  too: the standard simplex `conv{(0,0),(1,0),(0,1)}` has `L = (t+1)(t+2)/2`, so its period is 1 but
  its coefficient lcm is 2.
- **Integer programming.** `T` is cut out by integer data `Ax ≤ b`: `−y ≤ 0`, `−x+2y ≤ 0`,
  `x+2y ≤ 2`. Its vertex denominators have lcm 2. Its basis subdeterminants are `|det| = 1, 1, 4`
  over the pairs of rows, with lcm 4. Both differ from the period 1.

**Not refuted (true readings):**
- the weak vertex form "the lcm is *a* period" (Ehrhart's theorem);
- the lattice-only reading with vertex or facet denominators;
- the reading where "denominators" means the cyclotomic factors (poles) of the reduced Ehrhart series.
  The minimal period is the lcm of the orders of those roots of unity, so this reading is true. For
  `T` the series is `1/(1−z)³`.

## Contents

- `report.tex`, `report.pdf`: the complete mathematical report.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent check using only the Python standard library. It counts lattice
  points from the vertices by exact barycentric coordinates and derives the facets from the
  vertices. It finds minimal periods by exact interpolation of the residue classes (`t ≤ 60`), and
  it also checks the McAllister–Woods triangles `conv{(0,0),(1,(D−1)/D),(D,0)}` for `D = 2..6`.
- `verification.txt`: the build log, the forbidden-token scan and the Python output.

## Lean

All objects are defined from scratch:
- rational triangles by their vertices (`Tri`), with `Tri.denLcm` the lcm of the vertex denominators;
- membership of a lattice point in the dilate `tP` through rational convex weights
  (`Tri.MemScaled`, denominators cleared);
- facet inequalities (`Facet`, `facetDenLcm`, `FacetsOf`);
- the lattice-point count `hcount`, an explicit count over a finite box, and `Describes`, which
  says that the box and the facet list capture exactly the lattice points of every `tP`;
- quasi-polynomials with period `p` (`HasPeriod`: `D·L(t) = P_{t mod p}(t)` with integer polynomials
  `P_r` and `D > 0`) and minimal periods (`IsMinPeriod`, proved unique).

Main results:
- `describes_T`: the V-description and the H-description of `T` agree on all lattice points.
- `LT_formula`: `2·L_T(t) = (t+1)(t+2)`, proved by the recurrence `L_T(t+2) = L_T(t) + 2t + 5`.
- `LT_minPeriod`, `LT_not_minPeriod_two`, `T_denLcm`: the minimal period is `1`, but the lcm is `2`.
- `conjecture_00000007130_false : ¬ VertexClaim`. `VertexClaim` is the clause for all rational
  triangles.
- `L2_formula`, `L2_minPeriod`: `T₂` has minimal period exactly `2`. Period `1` is excluded by a
  divisibility argument: `a − b ∣ P(a) − P(b)` with `a = 2D+1`.
- `conjecture_00000007130_false_facet`, `conjecture_00000007130_false_facet_weak`: the facet reading
  fails, in both the "the period" and the "a period" forms.
- Non-vacuity: `LT_period_denLcm` (`2` is a period of `L_T`), `sanity_T2_vertex` and
  `sanity_T_facet`. The claimed equality does hold in these other instances.
- Not in Lean: the coefficient-denominator reading, the standard-simplex example and the
  integer-programming subdeterminants. They are covered by the report and `verify.py`.

There is no `sorry`, no `native_decide` and no added axiom. `#print axioms` shows at most
`propext`, `Classical.choice` and `Quot.sound`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想声称：Ehrhart 拟多项式的周期等于分母的最小公倍数。猜想是合取命题，我们否定这一子句。
反例是 McAllister–Woods 所说的"周期坍缩"：三角形 `T = conv{(0,0),(1,1/2),(2,0)}` 的顶点坐标分母的最小公倍数为 2，
但对一切 `t ≥ 0` 都有 `#(tT ∩ ℤ²) = (t+1)(t+2)/2`。所以其 Ehrhart 拟多项式其实是多项式，（最小）周期为 1 ≠ 2。
证明：整点 `(x,y) ∈ tT` 当且仅当 `y ≥ 0`、`2y ≤ x`、`x+2y ≤ 2t`。第 `y` 行有 `2t+1−4y` 个整点，按 `t` 的奇偶分别求和即得。

关于各种解读：
- "周期"指最小周期。2 仍然是 `L_T` 的一个周期（Ehrhart 定理）。若把子句理解为"lcm 是一个周期"并取顶点分母，则子句为真，这一点我们如实说明。
- 若"分母"指刻面不等式 `a·x ≤ b`（`a` 为本原整向量）右端 `b` 的分母，则对照三角形 `T₂ = conv{(0,0),(1,0),(0,1/2)}` 给出反例。
  其刻面为 `x ≥ 0`、`y ≥ 0`、`x+2y ≤ 1`，lcm 为 1，但 `4·#(tT₂ ∩ ℤ²) + (t mod 2) = (t+2)²`，周期恰为 2。
  1 甚至不是它的一个周期，所以弱形式也被否定。
- 若"分母"指拟多项式系数的分母，则 `T` 的 Ehrhart 多项式 `t²/2+3t/2+1` 的系数分母的 lcm 为 2 ≠ 1，同样不成立。
- 若取顶点分母或刻面分母，则只考虑格点多面体的解读平凡成立（"1 = 1"）。拟多项式、周期、分母这些概念只在有理多面体上才有意义，所以我们采用有理多面体的解读。
  若取系数分母，则格点多面体的解读同样不成立：标准单形 `conv{(0,0),(1,0),(0,1)}` 满足 `L = (t+1)(t+2)/2`，周期为 1，但系数分母的 lcm 为 2。
- 整数规划解读：`T` 由整数数据 `Ax ≤ b` 给出（`−y ≤ 0`、`−x+2y ≤ 0`、`x+2y ≤ 2`）。其顶点分母的 lcm 为 2，基子行列式绝对值为 1、1、4，lcm 为 4，两者都不等于周期 1。
- 未被否定（为真）的解读：顶点分母的弱形式"lcm 是一个周期"（Ehrhart 定理）；取顶点或刻面分母时只考虑格点多面体的解读；
  "分母"指约化 Ehrhart 级数分母中的分圆因子（单位根极点）的解读。最小周期正是这些单位根阶数的 lcm，因此该解读为真。

Lean 项目（Lean 4.19.0，仅核心库）从零定义了有理三角形、伸缩 `tP` 中的整点（凸组合权）、刻面不等式、有限盒中的整点计数、
拟多项式的周期与最小周期。项目证明了 `¬ VertexClaim`、`¬ FacetClaim` 及其弱形式，并验证了非空性。Python 脚本用独立方法复核了全部数值。
