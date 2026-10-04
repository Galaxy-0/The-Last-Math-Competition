# Counterexample to conjecture 00000001564

The conjecture states: "A cs-neighborly polytope is centrally symmetric and has support points in every
direction. The minimal number of vertices of a k-dimensional cs-neighborly polytope is
2^{k+1}, and the extremal bodies are the Hanner polytopes."

**The first clause is false for every k ≥ 1.** The k-dimensional cross-polytope
`conv{±e_1, …, ±e_k}` has these properties:

- it is k-dimensional;
- it is centrally symmetric;
- it has only **2k < 2^{k+1}** vertices;
- it is cs-neighborly in the strongest sense: **every** set of its vertices that contains no
  antipodal pair `{v, −v}` is the vertex set of a face. The maximizers of the functional
  `Σ_{s∈S} s` are exactly `S`.

Smallest cases:

| k | polytope | vertices | claimed minimum 2^{k+1} |
|---|---|---|---|
| 1 | segment | 2 | 4 |
| 2 | square | 4 | 8 |
| 3 | octahedron | 6 | 16 |

The conjecture is a conjunction, so refuting this one clause refutes it.

**Readings covered.** The counterexample satisfies every reading of "cs-neighborly":

- the statement's literal definition (central symmetry plus a support point in every direction,
  which every polytope has);
- Grünbaum's cs-j-neighborliness for every j, including j = 2 (any two non-antipodal vertices
  span an edge) and j = ⌊k/2⌋;
- the strongest form above.

It also works when k is read as the neighborliness parameter instead of the dimension.

**The Chinese reading (dimension 2k).** The Chinese text says "二 k 维", which is 2k-dimensional.
Read that way, the clause says that every 2k-dimensional cs-neighborly polytope has at least
2^{k+1} vertices, with equality attained, for all k ≥ 1.

- The true minimum in dimension 2k is 4k.
- So this reading **holds for k = 1, 2** (4 = 4, 8 = 8) and **fails for every k ≥ 3**.
- The smallest counterexample is the 6-dimensional cross-polytope: it has **12 < 16** vertices and
  property (F).
- Lean proves this as `conjecture_00000001564_false_2k`, using `crossFacts_6`.

**Further results** (proved in the report):

- The true minimum is **2k**. Every k-dimensional centrally symmetric polytope has at least 2k
  vertices, and equality holds exactly for affine cross-polytopes.
- A d-dimensional Hanner polytope has between 2d and 2^d vertices. So no Hanner polytope has
  2^{d+1} vertices, and the two clauses of the conjecture cannot both hold (for the k-dimensional reading, if "extremal" means attaining the minimum).

## Contents

- `report.tex`, `report.pdf`: the complete proof, the readings, the true minimum, and the Hanner
  vertex counts.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent check using only the Python 3 standard library. It uses a
  different method from the Lean proof:
  - it enumerates all small functionals and confirms that the faces of the cross-polytope are
    exactly the antipodal-free vertex sets, for k ≤ 6;
  - it checks the lower bound 2k on all centrally symmetric sets in {−1,0,1}^k for k = 2, 3;
  - it builds the explicit Hanner polytopes of dimension at most 6 and checks their vertex
    numbers.
- `verification.txt`: the fresh build log, the forbidden-token scan and the output of `verify.py`.

## Lean

All objects are defined from scratch. Points of ℤ^k are lists of integers.

- `IsVertex`: the unique maximizer of some functional.
- `ConvexPosition`: the polytope `conv V` has exactly `V.length` vertices.
- `IsFace V S`: `S` is exactly the set of maximizers of some functional.
- `CentSymm`: the vertex list is closed under negation.
- `FullDim`: a dimension certificate. `fullDim_sound` proves that it yields k linearly
  independent edge vectors.
- The three readings: `StatementCsNeighborly`, `CsNeighborlyUpTo j` and `CsNeighborlyFull`.
- `MinVerticesIs N k n` says that the minimum is attained and is a lower bound.
  `MinClause N := ∀ k ≥ 1, MinVerticesIs N k (2^(k+1))`.

The facts about `cross k` for k = 1, 2, 3, 4, 6 are checked by `decide`. For k = 6 this uses
`decide +kernel` and takes about 70 s.

- length 2k, no repetitions, central symmetry;
- the vertex witnesses and the dimension certificate;
- for every antipodal-free subset, the face witness `Σ S`.

Main theorems:

- `conjecture_00000001564_false : ¬ MinClause StatementCsNeighborly`;
- `conjecture_00000001564_false_grunbaum (j) : ¬ MinClause (CsNeighborlyUpTo j)`;
- `conjecture_00000001564_false_full : ¬ MinClause CsNeighborlyFull`;
- `conjecture_00000001564_false_any`: the same for any notion N that the octahedron satisfies;
- `conjecture_00000001564_false_param`: k read as the neighborliness parameter;
- `conjecture_00000001564_false_2k (N) (hN : N (cross 6)) : ¬ ∀ k, 1 ≤ k → MinVerticesIs N (2*k) (2^(k+1))`
  is the Chinese 2k-dimensional reading. It has instances `_2k_statement`, `_2k_full`,
  `_2k_grunbaum (j)` and `_2k_cs3`;
- `fails_each_k`: the clause fails separately at k = 1, 2, 3, 4;
- `conjecture_00000001564_conjunction_false`: the conjunction is false whatever the Hanner clause is.

Non-vacuity:

- `true_min_k1` proves a true instance, `MinVerticesIs _ 1 2`.
- `hexagon_not_csNeighborly`: a centrally symmetric hexagon satisfies the literal definition but
  is not cs-2-neighborly.
- `not_convexPosition`: a set with an interior point is not in convex position.

Hanner polytopes: `HannerCount` generates the (dimension, vertex number) pairs from segments,
products and free sums. `hanner_bounds` proves 2d ≤ v ≤ 2^d, and `no_hanner_with_2pow_succ`
proves v ≠ 2^{d+1}.

The project has no `sorry`, no `native_decide` and no added axioms. `#print axioms` shows only
`propext`, `Quot.sound`, and `Classical.choice` for the generic linear-independence lemma.

**Scope.**

- Lean verifies the cross-polytope for k = 1, 2, 3, 4, 6; one k is enough to refute the clause. The case
  of general k is proved in the report.
- The general lower bound 2k is formalized only for k = 1.
- For Hanner polytopes, only the vertex-count recursion is formalized.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想断言：k 维 cs-邻居多胞体的最小顶点数为 2^{k+1}，并且极值体是 Hanner 多胞体。第一条对所有 k ≥ 1 都不成立。

k 维正轴体（交叉多胞体）conv{±e_1, …, ±e_k} 有以下性质：

- 维数为 k，且中心对称；
- 只有 2k < 2^{k+1} 个顶点；
- 它满足最强意义下的 cs-邻居性：任何不含对径点对的顶点集都是某个面的顶点集，由线性泛函 Σ_{s∈S} s 恰好取到。

最小的例子：线段（2 < 4）、正方形（4 < 8）、正八面体（6 < 16）。

中文题面写的是“二 k 维”，即 2k 维。按这种读法，命题断言 2k 维 cs-邻居多胞体的最小顶点数为 2^{k+1}，其中包含全称下界：每个 2k 维 cs-邻居多胞体至少有 2^{k+1} 个顶点。

- 2k 维的真实最小值是 4k，所以该读法在 k = 1, 2 时成立（4 = 4，8 = 8），对所有 k ≥ 3 不成立。
- 最小反例是 6 维正轴体，它有 12 < 16 个顶点。
- Lean 定理 `conjecture_00000001564_false_2k` 证明了这一点。

这一反例覆盖以下各种解读：

- 题面字面定义（中心对称并且各方向都有支撑点，任何多胞体都满足后者）；
- Grünbaum 的 cs-j-邻居性（任意 j）；
- 把 k 理解为邻居性参数的读法。

报告还证明了以下事实：

- 真实最小值是 2k，且恰由仿射正轴体取到；
- d 维 Hanner 多胞体的顶点数介于 2d 与 2^d 之间，因此不存在顶点数为 2^{d+1} 的 Hanner 多胞体，猜想的两条结论本身就互相矛盾（指 k 维读法，且“极值体”理解为达到最小值者）。

Lean（4.19.0，仅核心库）从零定义了顶点、面、中心对称、维数证书和三种 cs-邻居性，并具体完成了以下工作：

- 用 decide 对 k = 1, 2, 3, 4 验证正轴体的全部性质；
- 证明主定理 `conjecture_00000001564_false` 等；
- 给出非空性检查以及 Hanner 顶点数的界。

verify.py 只用 Python 标准库，以不同的方法独立复核上述结果。
