# Counterexample to conjecture 00000009617

The conjecture says, among other things, that **the Fisher (Fischer) minimal state count of a sofic
shift equals the rank of the Hankel matrix of its language**. This clause is false. The conjecture
is a conjunction, so it is false as a whole. Its two later clauses (a local polynomial-time
criterion on words of length 2n+1, and uniqueness of the minimal graph) are not addressed.

**Counterexample: the even shift** `X`. Its points are the bi-infinite 0/1 sequences that contain no
block `0 1^(2k+1) 0`, so every run of 1s between two 0s has even length.

- **Fischer cover: 2 states.** The cover is `A -0-> A`, `A -1-> B`, `B -1-> A`. It is
  right-resolving, irreducible and follower-separated, and its bi-infinite path labels are exactly
  `X`. No labelled graph with at most 1 vertex presents `X`:
  - a single vertex with loop labels `T` presents `T^Z`;
  - `T = {0}` misses `1^∞`, `T = {1}` misses `0^∞`, and `T = {0,1}` contains `…0001000…`,
    which is not in `X`.

  So the minimal number of states is 2, both over right-resolving presentations and over all
  presentations.
- **Hankel rank: 3.** The Hankel matrix is `H[u][v] = [uv ∈ L(X)]`. Take rows `11, 0, 01` and
  columns `0, 10, 1`:

  |      | 0 | 10 | 1 |
  |------|---|----|---|
  | 11   | 1 | 1  | 1 |
  | 0    | 1 | 0  | 1 |
  | 01   | 0 | 1  | 1 |

  This minor has determinant −1 and the integer inverse `[[1,0,−1],[1,−1,0],[−1,1,1]]`. So the rank
  is at least 3 over **every field**. The rank is exactly 3, because `H` has only four distinct
  rows (the follower sets `L`, `F(0)`, `F(01)` and `∅`).

**Readings.** The standard rank of a matrix (over ℚ, ℝ, ℂ, 𝔽_p, or any field) is refuted. "Fisher
count" may mean the minimal right-resolving presentation, any presentation, or the left Fischer
cover; it is 2 under all three. Any indexing of `H` by words of length ≥ 2 contains the minor.

**Disclosure.** Under the non-standard *Boolean* rank (OR/AND semiring), the row of `ε` equals
`row(0) OR row(01)` and the Boolean rank is 2. So this example does **not** refute a Boolean-rank
reading. We make no claim about that reading.

## Contents

- `report.tex`, `report.pdf`: the complete argument, the readings, and the proof that the rank is
  exactly 3.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py` (Python 3 standard library) checks:
  - three descriptions of `L(X)` agree on all words of length ≤ 14;
  - an exhaustive search over all labelled graphs with ≤ 2 vertices;
  - the minor, its determinant and its inverse;
  - the rank 3 of the Hankel truncation on all words of length ≤ 6, over ℚ and over 𝔽₂, 𝔽₃, 𝔽₅, 𝔽₇;
  - the four distinct rows;
  - the Boolean-rank identity.
- `verification.txt`: the fresh build log, the forbidden-token scan and the Python output.

## Lean

- **Definitions.**
  - Points are `Int → Bool`. `EvenShift` is defined by the forbidden blocks `0 1^(2k+1) 0`.
  - `Lang X w` means that `w` occurs in some point of `X`.
  - `Presents E X` means that `X` equals the set of bi-infinite path labels of the labelled graph
    `E`. `RightResolving` and `Sofic` are defined from it.
  - `IsFisherCount X m` means that `m` is the least number of vertices of a right-resolving
    presentation. `IsMinPresCount` is the same for arbitrary presentations.
  - `hankelEntry X u v` is 1 or 0 according to `Lang X (u ++ v)`.
  - `HankelRankAtLeast X r` means that some `r×r` minor has a nonzero integer determinant (rank over
    ℚ). `HankelRankAtLeastMod p` is the same over ℤ/p. `HankelRankIs X m` means "at least `m` and
    not at least `m+1`".
- **Results.**
  - `lang_iff` characterises `L(X)` for **all** words.
  - `fisher_sound` and `fisher_complete` prove that the 2-state graph presents `X`, in both
    directions. The second builds the bi-infinite path.
  - `no_zero_state` and `no_one_state` exclude smaller presentations of any kind.
  - `fisher_count` and `min_presentation_count` prove that the minimal state count is 2.
  - `minor_det` gives `= -1`. `minor_unimodular` checks the integer inverse. `rows_independent` shows
    that the three rows are linearly independent over ℚ.
  - `hankel_rank_ge_three` gives rank ≥ 3 over ℚ, and `hankel_rank_ge_three_mod` gives rank ≥ 3
    over ℤ/p for every p ≥ 2.
- **Main theorems.**
  - `conjecture_00000009617_false : ¬ Claim`, where `Claim` is "for every sofic `X`, Fisher count
    `m` ⇒ Hankel rank `= m`".
  - `conjecture_00000009617_false_mod p` covers ℤ/p for every p ≥ 2.
  - `conjecture_00000009617_false_any_presentation` covers arbitrary presentations.
  - `fisher_lt_rank` shows that the Fisher count is 2 and the rank is at least 3.
- **Not in Lean.** The upper bound rank ≤ 3 and the Boolean-rank remark are in the report and in
  `verify.py`.

The project has no `sorry`, no `native_decide`, and no added axioms. `#print axioms` shows only the
standard `propext`, `Classical.choice` and `Quot.sound`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想中有一条子句：sofic 移位的 Fisher（Fischer）最小状态数等于其语言 Hankel 矩阵的秩。这一条不成立。猜想是若干子句的合取，所以整个猜想为假。后两条子句（长 2n+1 词的局部判据、最小图结构唯一）本文不涉及。

**反例：偶移位 X**（禁止块 `0 1^(2k+1) 0`，即两个 0 之间的 1 串长度都是偶数）。

- **Fischer 覆盖有 2 个状态**：A-0->A，A-1->B，B-1->A。它是右可解的，其双向无限路径的标签集恰为 X。任何至多 1 个顶点的带标号图都不能呈现 X：单顶点图呈现 T^Z，而 T={0}、{1}、{0,1} 都不对。所以无论只考虑右可解呈现还是考虑任意呈现，最小状态数都是 2。
- **Hankel 矩阵 H[u][v]=[uv∈L(X)] 的秩为 3**：取行 11、0、01 和列 0、10、1，得到子式 [[1,1,1],[1,0,1],[0,1,1]]，其行列式为 −1，并且有整数逆矩阵。所以在任何域上秩都至少为 3。又因为 H 只有 4 种不同的行（其中一行为零），秩恰为 3。

按标准的（域上的）秩，猜想被否定。说明：若把"秩"理解为非标准的布尔秩（OR/AND 半环），则该例给出 2=2，不构成反例；对这种理解我们不作任何断言。

Lean 项目（Lean 4.19.0，仅用核心库）从定义出发形式化了以下内容：偶移位、语言、带标号图的呈现、Fisher 最小状态数（右可解呈现以及任意呈现）、Hankel 矩阵、行列式与秩，并证明了 `¬ Claim`（ℚ 上）以及对一切 p≥2 在 ℤ/p 上的版本。Python 脚本用不同的方法独立验证了全部数值。
