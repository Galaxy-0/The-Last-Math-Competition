# Disproof of conjecture 00000000297

The conjecture makes three claims:

1. There is an aperiodic rotation-free set of only 2 Wang tiles.
2. No single Wang tile is aperiodic.
3. Hence the minimal rotation-free aperiodic set has size exactly 2.

**Claim 1 is false, so claim 3 and the conjecture are false.** Claim 2 is true.

**Theorem.** Let `T` be a set of at most two Wang tiles, with arbitrary edge colors.
If `T` tiles the plane, then it has a tiling with periods `(2,0)` and `(0,2)`.

So no set of at most 2 Wang tiles is aperiodic. This holds in the strong sense (no
tiling has any nonzero period) and in the weak sense (no tiling is doubly periodic).
It also holds whether "only 2" means exactly 2 or at most 2. This agrees with
Jeandel–Rao, who found that the smallest aperiodic Wang set has 11 tiles. Their result
is not used here.

**Proof idea.** Let `f` be a tiling by `{t0, t1}`.

- **Local lemma.** Suppose `t0 | t1` and `t1 | t0` do not both hold (`|` means
  "east color = west color"). Then every tile in `f` matches itself horizontally.
  Indeed, if the tile at `(x,y)` did not, both of its horizontal neighbours would be
  the other tile, which gives both cross matches.
- The same holds vertically.
- Four cases follow. Each gives a period-2 tiling:
  - **Checkerboard:** cross matches in both directions.
  - **Constant:** no cross matches in either direction.
  - **Horizontal stripes:** vertical cross matches only.
  - **Vertical stripes:** horizontal cross matches only.
- In the stripe cases, compare `f(0,0)` with its neighbour. If they are equal, the
  constant tiling works. If they differ, both tiles occur, so both match themselves.

## Contents

- `report.tex`, `report.pdf`: the complete proof and the reading of the conjecture.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent exhaustive check (Python 3 standard library). It covers:
  - all 256 pairs of horizontal/vertical compatibility relations on two tiles: either
    no legal 3×3 square exists, or a legal 2×2 torus exists;
  - all 6561 ordered pairs of concrete tiles with colors in {0,1,2};
  - the four patterns of the proof.
- `verification.txt`: the build log, the axiom audit and the Python output.

## Lean

- **Objects.**
  - `Tile C` has fields `n e s w : C`, for any color type `C`.
  - `IsTiling T f` takes `f : Int → Int → Tile C` with values in the list `T` and
    requires matching edges.
  - `IsPeriodic`: a nonzero period.
  - `IsDoublyPeriodic`: two periods with nonzero determinant.
  - `Aperiodic` (strong) and `WeaklyAperiodic`.
- **Local lemma:** `hloop`, `vloop`.
- **Main results:**
  - `two_tiles_periodic`: the two-tile case.
  - `le_two_tiles_periodic`: every list `T` with `T.length ≤ 2` that tiles also has a
    tiling with periods `(2,0)` and `(0,2)` that is periodic and doubly periodic.
- **The conjecture:**
  - `conjecture_00000000297_false : ¬ Conjecture297 C` for every color type `C`, where
    `Conjecture297 C := Clause1 C ∧ Clause2 C ∧ MinAperiodicSize C 2`.
  - `clause1_false`: no 2-tile set is aperiodic.
  - `clause1_weak_false`: the same with "weakly aperiodic".
  - `clause1_le_false`: the same for sets of at most 2 tiles.
  - `minSize_ne_two`.
  - `clause2_true`: claim 2 holds.
- **Non-vacuity:**
  - `tiles_example`: a 2-tile set that tiles.
  - `not_tiles_example`: a 2-tile set that does not tile.
  - `crossTiling_isTiling`, `crossTiling_not_periodic`: a genuine tiling, by a 4-tile
    set, with no nonzero period.

The project has no `sorry`, no `native_decide` and no added axioms. `#print axioms`
shows only `propext`, `Classical.choice` and `Quot.sound`.

**Scope.** The conjecture's definition fixes the setting to Wang tiles: edge-colored
unit squares placed by translation only. Nothing is claimed about prototiles of
general shape. (That is a different setting. Greenfeld–Tao, DCG 2023, give an aperiodic pair of
translational tiles in Z²×G₀ with G₀ finite abelian.) Tiles are placed by translation only:
`IsTiling` has no rotations.

**Reading of "aperiodic".** "Aperiodic prototile set" is the standard term of art: the set tiles the plane
and *every* tiling by it is non-periodic. A set that merely admits some non-periodic tiling is not
aperiodic. For example, (n,e,s,w) = (0,1,0,1) and (0,2,0,2) force constant rows that can be stacked in
any order. That loose reading is non-standard, and we set it aside.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想由三部分组成：

1. 存在仅 2 张、免旋转的非周期 Wang 瓦片集；
2. 不存在单张非周期瓦片；
3. 因而最小非周期集的大小恰为 2。

**第 1 条是错的，因此第 3 条和整个猜想都不成立。** 第 2 条是对的。

**定理：** 任意至多 2 张的 Wang 瓦片集（颜色任意）若能铺满平面，则存在一个以
`(2,0)` 和 `(0,2)` 为周期的铺砌。因此至多 2 张的 Wang 瓦片集都不是非周期的：
无论按强意义（任何铺砌都没有非零周期）还是弱意义（任何铺砌都不是双周期）理解都是如此。

**证明要点：** 局部引理是这样的：若 `t0、t1` 不能在水平方向互相拼接，则铺砌中每块瓦片都能与自身水平拼接。
理由是：否则它左右两侧都必须是另一张瓦片，从而两种交叉拼接都成立，矛盾。竖直方向同理。
由此分四种情形，分别得到常值、棋盘、横条纹或竖条纹铺砌，它们都以 2 为周期。

Lean（仅核心库）从零定义了 Wang 瓦片、铺砌、周期性和（强/弱）非周期性，并完整证明了上述定理以及
`conjecture_00000000297_false`。`verify.py` 用另一种方法独立验证：对两块瓦片全部 256 种兼容关系做穷举，
结果是：要么 3×3 方块无法合法填满，要么存在合法的 2×2 环面图案。这与 Jeandel–Rao 的结果
（最小非周期 Wang 集有 11 张瓦片）一致。
