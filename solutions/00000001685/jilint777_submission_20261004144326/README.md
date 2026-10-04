# Disproof of conjecture 00000001685 (even subdivisions of K₃,₃ are not Pfaffian)

The conjecture says that the minimal families of nonplanar Pfaffian graphs are the
Möbius ladders M₂ₖ and the **even subdivisions of K₃,₃**, and that these two families
make up the nonplanar Pfaffian class of crossing number ≤ 2. So it asserts that every
even subdivision of K₃,₃ is a Pfaffian graph. That is false: **no even subdivision of
K₃,₃ is Pfaffian**, including K₃,₃ itself. K₃,₃ is also the Möbius ladder on 6 vertices.

**Why.** K₃,₃ has 6 perfect matchings, and every edge lies in exactly 2 of them.

- Reversing an edge flips the Pfaffian terms of exactly the matchings through that
  edge.
- So the parity of the number of negative terms is the same for every orientation.
- For one orientation, 3 of the 6 terms are negative, so the count is odd.
- A Pfaffian orientation (|Pf| = number of perfect matchings, i.e. all terms of one
  sign) would need that count to be 0 or 6.

Hence |Pf(A_D)| ∈ {0, 4} for all 2⁹ orientations D, never 6.

Subdividing an edge twice keeps all three facts (6 matchings, even edge counts, odd
parity), so by induction every even subdivision of K₃,₃ is non-Pfaffian. This holds
whether or not K₃,₃ itself counts, and whether some or all edges are subdivided.

**Readings covered.**

- **Pfaffian:** both definitions are refuted, the conjecture's own (|Pf| = #PM) and
  Kasteleyn's (all terms have the same sign).
- **"Minimal", "nonplanar":** any extra property attributed to the family is allowed;
  it is the parameter `Q` in Lean.
- **M₂ₖ, vertex-count convention:** M₆ ≅ K₃,₃ and M₁₀ are not Pfaffian either.
- **M₂ₖ, rung-count convention:** the ladders with 2, 4 and 6 rungs are Pfaffian. No
  claim is made against the Möbius part, and none is needed.
- **Secondary result:** the Wagner graph V₈ with one edge subdivided twice is
  Pfaffian, nonplanar, has crossing number ≤ 1, and lies in neither family. This
  refutes the second sentence read as "every nonplanar Pfaffian graph with crossing
  number ≤ 2 is in one of the families". It is proved in the report and checked in
  `verify.py`, not in Lean.

## Contents

- `report.tex` and `report.pdf`: the complete proof.
- `lean4/`: a Lean 4.19.0 project (core library only).
- `verify.py`: an independent check (Python 3 standard library).
  - It uses det(A_D) = Pf(A_D)² and tests whether det = (#PM)² for some orientation.
  - It checks exhaustively K₃,₃, S (one edge subdivided twice), K₃,₃ with two edges
    subdivided twice, and M₁₀.
  - It checks K₃,₃ with all edges subdivided 2 or 4 times, up to vertex switching.
  - It checks the parity obstruction for 515 even subdivisions, and Möbius ladders
    with 2 to 7 rungs.
- `verification.txt`: the fresh build log, the forbidden-token scan and the Python
  output.

## Lean

- **Definitions, from scratch.**
  - Graphs are edge lists.
  - Perfect matchings are edge masks covering each vertex exactly once (`PMs`).
  - Orientations are `List Bool`.
  - `term` is the sign of the permutation t₁h₁t₂h₂… and `Pf = Σ term`.
  - `IsPfaffian G`: some orientation has `|Pf| = numPM`. `IsPfaffian'`: all terms are
    equal.
- `not_pfaffian_of_invariant` proves the parity obstruction for **all** loopless
  graphs.
- `K33_not_pfaffian`, `S_not_pfaffian` and `M6_not_pfaffian` are the instances,
  checked by kernel `decide`.
- `EvenSubdivisionK33` is the inductive family generated from K₃,₃ by `subdivide2`.
- Main theorems:
  - `conjecture_00000001685_false (Q) : ¬ ∀ G, EvenSubdivisionK33 G → Q G ∧ IsPfaffian G`
  - `conjecture_00000001685_false'`: the same with Kasteleyn's definition.
  - `conjecture_00000001685_false_proper`: members other than K₃,₃.
  - `conjecture_00000001685_conjunction_false`.
  - `mobius_clause_false_vertex_convention`.
- Non-vacuity and cross-checks:
  - `K4_pfaffian` and `M8_pfaffian` (the nonplanar Wagner graph) give explicit Pfaffian
    orientations.
  - `pfMat_K33` and `pfMat_M8` agree with the matrix Pfaffian computed by row
    expansion.
- **Not in Lean:**
  - the induction over all even subdivisions; Lean covers K₃,₃ and S, which suffice
    for every reading;
  - invariance under relabelling;
  - the secondary result.
- There is no `sorry`, no `native_decide` and no added axiom. `#print axioms` shows at
  most `propext` and `Quot.sound`.

## Reproduce

```sh
cd lean4 && lake build          # about 1 minute
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想声称：非平面 Pfaffian 图的最小族是 Möbius 梯 M₂ₖ 与 K₃,₃ 的偶细分，并且这两族穷尽交叉数 ≤2 的非平面
Pfaffian 图。因此猜想断言 K₃,₃ 的每个偶细分都是 Pfaffian 图。这是错的：**K₃,₃ 的任何偶细分都不是 Pfaffian 图**，
K₃,₃ 本身也不是（它同时是 6 个顶点的 Möbius 梯）。

证明是经典的奇偶性论证。K₃,₃ 有 6 个完美匹配，每条边恰好属于其中 2 个。翻转一条边的方向，恰好改变经过该边的那些匹配项的符号。
因此在任何定向下，负项个数的奇偶性都不变。在参考定向下，负项有 3 个，是奇数。
而 Pfaffian 定向（|Pf| 等于完美匹配数，即所有项同号）要求负项个数为 0 或 6。所以 |Pf| 只能是 0 或 4，永远不等于 6。
把一条边细分两次时，匹配数、每条边所在匹配数为偶数、负项个数为奇数这三条性质都保持不变，由归纳法可知所有偶细分都不是 Pfaffian 图。
因此无论偶细分是否包括 K₃,₃ 本身、是否要求细分部分边或全部边，结论都成立。
M₂ₖ 若按顶点数理解，M₆ 和 M₁₀ 也不是 Pfaffian 图；若按横档数理解，我们不对 Möbius 部分作任何断言。

Lean 部分（仅用核心库）从头定义了图、完美匹配、定向和 Pfaffian 项，对所有图证明了上述奇偶性障碍定理，
用核验 `decide` 验证了 K₃,₃、S（一条边细分两次）和 M₆ 满足障碍条件，最后证明
`¬ ∀ G, EvenSubdivisionK33 G → Q G ∧ IsPfaffian G`。
`verify.py` 用另一种方法独立验证：利用 det = Pf² 穷举所有定向。
