# Proof of conjecture 00000001091

The conjecture says that the **complete 10-arcs of PG(2,11) form a single
isomorphism class**. Since 11 is prime, PΓL(3,11) = PGL(3,11), so isomorphism
means projective equivalence: an invertible 3 × 3 matrix over F₁₁ maps one arc
onto the other.

**The conjecture is true.** Complete 10-arcs exist, and any two of them are
projectively equivalent. The proof is fully formalized in Lean 4 (core library
only).

## The argument

1. **Projectivities preserve complete arcs.** An invertible matrix permutes the
   points and lines and preserves incidence, so it maps complete k-arcs to
   complete k-arcs.
2. **Frame lemma.** Any 4 points of an arc can be moved to the frame
   e₁, e₂, e₃, (1,1,1). In Lean this is a product of four matrices taken from
   explicit, exhaustively checked tables.
3. **Symmetry reduction.**
   - The other points of the arc lie among the 72 points off the six sides of
     the frame quadrangle.
   - The 24 projectivities permuting the frame (a copy of S₄) split these 72
     points into 4 orbits, of sizes 12, 24, 24 and 12. The representatives are
     (1,2,3), (1,2,4), (1,2,5) and (1,3,4).
   - Take the first orbit that the arc meets, and move that point to the orbit
     representative. The arc now contains frame + representative and avoids the
     earlier orbits.
4. **Exhaustive search.** A backtracking search with a proved soundness theorem
   finds exactly 13 complete 10-arcs of this form. The four search trees have
   816, 497, 138 and 4 nodes.
5. **Certificates.** Each of the 13 arcs is mapped by an explicit invertible
   matrix onto the representative
   R = {(1,0,0), (0,1,0), (0,0,1), (1,1,1), (1,2,3), (1,3,2), (1,4,5), (1,6,8), (1,9,4), (1,10,9)}.

## Further facts (`verify.py`, independent code)

- **Counts through the frame.** 84 complete 10-arcs contain the frame. The other
  252 10-arcs through the frame are all subsets of conics.
- **One class.** All 84 complete 10-arcs have one canonical form.
- **Stabilizer.** It has order 60, with the element orders of A₅.
- **Total.** PG(2,11) has |PGL(3,11)| / 60 = 3,540,460 complete 10-arcs.
- **Size spectrum.** The complete arcs through the frame have sizes 7, 8, 9, 10
  and 12.
- **Literature.** Ball–Lavrauw, *Planar arcs* (arXiv:1705.10940), Corollary 8,
  based on Hirschfeld's Table 9.4, says that PG(2,11) has a unique complete arc
  of size q − 1 = 10. Their Example 3 is checked to be equivalent to R.

## Contents

- `report.tex`, `report.pdf`: the complete proof.
- `lean4/`: a Lean 4.19.0 project (core only).
- `verify.py`: an independent check using the Python standard library (about 20 s).
- `verification.txt`: the build log, axiom audit and Python output.

## Lean

**Main theorem**

```lean
theorem conjecture_00000001091 :
    (∃ A, IsCompleteArc 10 A) ∧
      ∀ A B, IsCompleteArc 10 A → IsCompleteArc 10 B → ProjEquiv A B
```

**Definitions**

- `F = Fin 11`, with vectors `V` and matrices `Mat`.
- `coord`: the 133 normalized points.
- `inc`: incidence, given by the dot product with the dual coordinates of a line.
- `Collinear`: the three points lie on a common line.
- `IsArc`, `IsComplete`, and `IsCompleteArc k A`, where `A` is a list of k
  distinct points.
- `IsInv M N`: N is a two-sided inverse of M.
- `MapsOnto M A B`: {M·a : a ∈ A} = B.
- `ProjEquiv A B := ∃ M N, IsInv M N ∧ MapsOnto M A B`.

**General lemmas.** Proved for all matrices and points, without enumeration:
the linear algebra lemmas, `collinear_act`, `map_complete`, the search
soundness theorem `search_sound`, `reduce`, `frame_lemma` and
`complete10_equiv`.

**Finite facts.** Checked by `decide +kernel`:

- `ptl_check`: the incidence masks;
- `T1ok`–`T4ok`: the frame tables;
- `g1ok`–`g4ok`: the S₄ data;
- `search1`–`search4`;
- `orbit_ok`: the 13 certificates;
- `R_complete`.

**Sanity theorems**

- `points_cover`, `points_distinct`: the 133 points are exactly the points of
  PG(2,11).
- `C10_not_complete`: ten points of a conic form a 10-arc that is *not*
  complete.

**Axioms.** Only `propext` and `Quot.sound`. There is no `sorry`, no
`native_decide` and no added axiom. A fresh build takes about 85 s.

**Limitation.** Collinearity is defined as "on a common line" (incidence). Its
equivalence with det = 0 is standard but not proved in Lean. The facts listed
under "Further facts" (84, A₅, spectrum) are checked by `verify.py` only.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想：PG(2,11) 中所有 complete 10-arc（10 个点、无三点共线、且不能再添加点的弧）只有一个同构类。
由于 11 是素数，PΓL(3,11) = PGL(3,11)，因此"同构"就是射影等价：存在 F₁₁ 上的可逆 3×3 矩阵把一个弧映到另一个弧。

**结论：猜想成立**，并已在 Lean 4（仅核心库）中完整形式化。主定理 `conjecture_00000001091` 断言：
complete 10-arc 存在，且任意两个 complete 10-arc 射影等价。

证明思路：

1. **射影变换保持完全弧。** 可逆矩阵保持点线关联，因此把 complete k-arc 映为 complete k-arc。
2. **标架引理。** 弧中任意四点可用射影变换送到标准标架 e₁, e₂, e₃, (1,1,1)。
   Lean 中由四张经穷举验证的矩阵表依次复合得到。
3. **对称性约化。**
   - 其余点只能落在标架四边形六条边之外的 72 个点中。
   - 保持标架的 24 个射影变换（同构于 S₄）把这 72 个点分成 4 个轨道，大小为 12、24、24、12。
   - 取弧所遇到的第一个轨道，把该点移到轨道代表元。
4. **穷举搜索。** 搜索程序的正确性已在 Lean 中证明，搜索恰好找到 13 个 complete 10-arc。
5. **轨道证书。** 对这 13 个弧，各给出一个显式可逆矩阵，把它映到代表元 R。

**独立验证（verify.py，仅用 Python 标准库，与 Lean 数据无关）：**

- 含标架的 complete 10-arc 共 84 个，全部属于同一轨道；
- 稳定子群阶为 60，元素阶分布与 A₅ 相同；
- 其余 252 个含标架的 10-arc 都包含在二次曲线中；
- PG(2,11) 中 complete 10-arc 的总数为 3,540,460；
- 含标架的 complete arc 的大小为 7、8、9、10、12。

**文献对照：** Ball–Lavrauw《Planar arcs》推论 8（依据 Hirschfeld 表 9.4）指出 PG(2,11) 中大小为 10 的 complete arc 唯一。
其例 3 已验证与 R 射影等价。

**局限：** 共线性按"位于同一条直线上"定义（关联结构定义），它与行列式为零的等价性是标准事实，但未在 Lean 中证明。
84、A₅ 与大小谱等附加事实仅由 verify.py 验证。
