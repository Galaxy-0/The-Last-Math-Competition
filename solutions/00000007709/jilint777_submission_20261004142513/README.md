# Counterexample to conjecture 00000007709

The conjecture's first clause says: **the order k of a convex rep-tile must be a perfect square or k = 2**.
This is false. The right triangle with legs in ratio 1 : 2 is a **rep-5 tile**, and 5 is neither a perfect square nor 2.
The conjecture is a conjunction, so refuting this clause refutes it.

Take `T = ABC` with `A = (0,0)`, `B = (10,0)`, `C = (0,5)`. Its squared sides are 25, 100 and 125. Add the points
`D = (2,4)` (foot of the altitude from A), `M1 = (1,2)`, `M2 = (6,2)` and `M3 = (5,0)`. Then T splits into five
congruent triangles, each with squared sides 5, 20 and 25 (ratio 1/√5):

| piece | vertices | similarity `f_i(z) = (a·z̄ + b)/5` |
|---|---|---|
| P1 | A D C | a = −1−2i, b = 10+20i |
| P2 | A M3 M1 | a = 2−i, b = 5+10i |
| P3 | M3 B M2 | a = 2−i, b = 30+10i |
| P4 | M1 M2 D | a = 2−i, b = 10+20i |
| P5 | M3 M2 M1 | a = −2+i, b = 25 |

Here `|a|² = 5`, and `f_i(T) = P_i`. The pieces cover T, and their interiors are pairwise disjoint.

## Readings

- **Every order** (the conjecture's own usage: its second clause puts *all* parallelograms into "order 4",
  although some of them are also rep-2 or rep-3): refuted by the triangle above. This is what Lean proves.
- **Copies only similar, not congruent**: a fortiori, since our pieces are congruent.
- **"The order" = least k ≥ 2**: refuted by the 1 × √3 rectangle. It is rep-3 (three strips, which are rotated
  copies), and it cannot be cut into 2 similar copies, congruent or not. The proof is a corner and area argument
  (report, Proposition 5). This part is in the report and `verify.py`, not in Lean. Under this reading the 1:2
  triangle itself is not a counterexample. Its least order is 4 with congruent pieces, or 2 with merely similar
  pieces (cut along the altitude). That is why the rectangle is needed here.
- **Orientation-preserving copies only**: the rectangle again. The triangle's pieces are mirror images, which the
  standard definition (Golomb) allows.

## Contents

- `report.tex`, `report.pdf`: the complete proof, written directly in ℝ².
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py` (Python 3 standard library): an exact rational check that uses a different method from the Lean
  proof. It checks:
  - the vertex images under `f_i` and the squared side lengths;
  - that each piece lies in T;
  - pairwise separating edge lines;
  - the area sum;
  - a grid of 14641 rational points;
  - the rep-3 dissection of the 1×√3 rectangle, exactly in ℚ(√3), and the area obstruction to a rep-2
    dissection with congruent pieces. The general non-rep-2 proof, which also covers pieces that are only
    similar, is in report Prop. 5(b) only.
- `verification.txt`: the build log, the forbidden-token scan and the output of `verify.py`.

## Lean

All objects are defined from scratch:

- **Points.** Points of ℚ² are homogeneous integer triples `(x, y, w)` with `w > 0`, standing for `(x/w, y/w)`.
- **Polygons.** `ConvexPolygon` is a counterclockwise vertex list in strictly convex position. `InPoly` and
  `InPolyInt` are the closed region and the interior, given by orientation determinants.
- **Similarities.** `IsSimilarity f n m` means `|f(P) f(Q)|² = (n/m)·|PQ|²` for all P, Q.
- **Rep-tiles.** `RepTile vs k` asks for k similarities, each with squared ratio 1/k, such that:
  - every piece lies in the tile;
  - the pieces cover the tile;
  - the images of the interior are pairwise disjoint.
- **The claim.** `Claim := ∀ vs, ConvexPolygon vs → ∀ k, RepTile vs k → (∃ m, k = m*m) ∨ k = 2`.

Main results:

- `T_rep5 : RepTile T 5`
- `conjecture_00000007709_false : ¬ Claim`

Supporting lemmas:

- `ConjAffine.isSimilarity`: polynomial identities showing that `z ↦ (a z̄ + b)/d` scales squared distances by
  `|a|²/d²`.
- `f_vertices`, `into`, `back1`–`back5`: these show `f_i(T) = P_i`.
- `pieces_sub`, `cover`, `disjoint`: linear arithmetic, closed by `omega`.
- Non-vacuity: `all_convex` shows that T and every piece are convex polygons, and `interiors_nonempty` gives a
  centroid inside T and inside each piece.

There is no `sorry`, no `native_decide` and no added axiom. `#print axioms` shows at most `propext`,
`Classical.choice` and `Quot.sound`.

**Scope:** Lean works in ℚ². The real case follows by density, since the pieces are closed rational triangles and
interiors are open (report, §5). The report's proof is also carried out directly over ℝ.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想的第一条断言：凸 rep-tile 的阶 k 必为完全平方数或 k = 2。这是错的。
两条直角边之比为 1 : 2 的直角三角形是 rep-5 tile，而 5 既不是完全平方数也不等于 2。

取 A = (0,0)、B = (10,0)、C = (0,5)，再取 D = (2,4)（A 到斜边的垂足）、M1 = (1,2)、M2 = (6,2)、M3 = (5,0)。
三角形 ABC 可剖分为 ADC、A M3 M1、M3 B M2、M1 M2 D、M3 M2 M1 五个全等三角形，
每个都与原三角形相似，相似比为 1/√5。每一块都是原三角形在相似变换 z ↦ (a z̄ + b)/5 下的像，其中 |a|² = 5。

若把"阶"理解为最小的 k ≥ 2，则 1:2 直角三角形本身不是反例：要求全等时它的最小阶为 4，只要求相似时为 2（沿高剖开）。
此时 1 × √3 的矩形是反例：它是 rep-3 的（三条竖条，都是旋转后的拷贝），
并且不能剖分成 2 个与它相似的部分（无论是否要求全等）。这一部分的证明只在报告和 verify.py 中，没有在 Lean 中形式化。

Lean 在有理平面 ℚ² 上从头定义了点、凸多边形、相似变换（用距离平方刻画）、rep-k tile 以及猜想的断言，
并证明了 `RepTile T 5` 和 `¬ Claim`。实平面的情形由稠密性推出，报告中的证明也直接在 ℝ² 上进行。
