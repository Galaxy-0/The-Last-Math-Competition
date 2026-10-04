# Counterexample to conjecture 00000009617

The conjecture says, among other things, that **the Fisher (Fischer) minimal state count of a sofic
shift equals the rank of the Hankel matrix of its language**. This clause is false when "rank" has
its standard meaning: rank over a field. The conjecture is a conjunction, so it is false as a whole.
Its two later clauses (a local polynomial-time criterion on words of length 2n+1, and uniqueness of
the minimal graph) are not addressed.

## Counterexample 1: the even shift `X`

`X` has no block `0 1^(2k+1) 0`, so every run of 1s between two 0s has even length.

- **Fischer cover: 2 states.** The cover is `A -0-> A`, `A -1-> B`, `B -1-> A`. It is
  right-resolving, irreducible and follower-separated, and its bi-infinite path labels are exactly
  `X`. No labelled graph with ≤ 1 vertex presents `X`:
  - a single vertex with loop labels `T` presents `T^Z`;
  - `T = {0}` misses `1^∞`, `T = {1}` misses `0^∞`, and `T = {0,1}` contains `…0001000…`.
- **Hankel rank: 3.** Rows `11, 0, 01` × columns `0, 10, 1` of `H[u][v] = [uv ∈ L(X)]` give
  `[[1,1,1],[1,0,1],[0,1,1]]`. This minor has determinant −1 and the integer inverse
  `[[1,0,−1],[1,−1,0],[−1,1,1]]`. So the rank is ≥ 3 over every field, and it is exactly 3 (4
  distinct rows, one of them zero).

## Counterexample 2: the charge-constrained shift `X_c`

`X_c` is presented by `0 -1-> 1 -1-> 2` and `2 -0-> 1 -0-> 0`: the running charge (+1 for 1, −1 for
0) stays in a band of width 2. The even shift has 3 nonempty follower sets, equal to its rank, so
`X_c` is needed for the follower-set reading.

- **Fischer count 3.** The graph is right-resolving, irreducible and follower-separated. Every
  graph with ≤ 2 vertices fails, by exhaustive search.
- **6 nonempty follower sets.** The terminal vertex sets are `{0,1,2}, {0,1}, {1,2}, {0}, {2}, {1}`,
  attained by `ε, 0, 1, 00, 11, 001`. With the dead state there are 7.
- **Hankel rank exactly 5 over every field.**
  - Lower bound: rows and columns `ε, 0, 1, 00, 11` give
    `[[1,1,1,1,1],[1,1,1,0,1],[1,1,1,1,0],[1,0,1,0,1],[1,1,0,1,0]]`, with determinant 1.
  - Upper bound: `1_F(ε) + 1_F(001) = 1_F(0) + 1_F(1)`, because `F_G(0) ∩ F_G(2) = {ε}`.
- **Conclusion.** The rank 5 differs from all of these:
  - the Fischer count 3;
  - the least size 3 of any presentation;
  - the 6 follower sets;
  - the 7 states of the complete minimal DFA.

## Readings

- **Refuted:** rank over ℚ, ℝ, ℂ, 𝔽_p, or any other field. This holds whether "state count" means:
  - the minimal right-resolving presentation;
  - any presentation;
  - the left Fischer cover;
  - the follower-set graph or the trim/complete minimal DFA (via `X_c`).
- **Not refuted: Boolean (OR/AND) rank.** The Boolean rank is always ≤ the Fischer count:
  - each row `F(w)` is the union of the follower sets of the Fischer vertices where `w` can end;
  - so `H` is a Boolean product through `n_Fischer`;
  - searches over small examples found equality in every case, so the clause may be true under this
    reading.

  We refute only the field-rank reading.
- **Measure (HMM) reading.** A Hankel matrix of the probabilities `P(w)` depends on the measure:
  - for a Markov measure carried by the Fischer cover, the rank is ≤ the Fischer count; it is 2 for
    the even shift with the Parry measure;
  - the point mass at `0^∞` gives rank 1.

  The clause says "Hankel matrix of its language", so we use the indicator of `L`.

## Contents

- `report.tex`, `report.pdf`: the complete argument, with proofs of the exact ranks and a discussion of
  the readings.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py` (Python 3 standard library) checks both shifts:
  - the languages, computed in independent ways;
  - exhaustive graph searches up to 2 vertices;
  - the minors;
  - the ranks of the truncations over ℚ and over 𝔽₂, 𝔽₃, 𝔽₅, 𝔽₇;
  - the follower-set counts;
  - the row relation;
  - the Boolean factorization and the measure examples.
- `verification.txt`: the fresh build log, the forbidden-token scan and the Python output.

## Lean

- **Definitions.**
  - Points are `Int → Bool`. `EvenShift` is defined by forbidden blocks.
  - `Lang X w` means that `w` occurs in some point of `X`.
  - `Presents E X` means that `X` equals the set of bi-infinite path labels of `E`.
    `RightResolving` and `Sofic` are defined from it.
  - `IsFisherCount X m` means that `m` is the least number of vertices of a right-resolving
    presentation. `IsMinPresCount` is the same for arbitrary presentations.
  - `hankelEntry` is defined from `Lang`.
  - `HankelRankAtLeast X r` means that some `r×r` minor has a nonzero integer determinant (rank over
    ℚ).
  - `HankelRankAtLeastMod p` means the determinant is nonzero mod `p`. It is proved for every p ≥ 2,
    in particular every prime. For composite `p`, ℤ/p is not a field, but the minors are unimodular.
- **Even shift.**
  - `lang_iff` characterises the language for all words.
  - `fisher_sound` and `fisher_complete` prove that the 2-state graph presents `X`, in both
    directions.
  - `no_zero_state` and `no_one_state` exclude smaller graphs of any kind.
  - `fisher_count` and `min_presentation_count` prove that the minimal state count is 2.
  - `minor_det` gives `= -1`, and `minor_unimodular` checks the inverse.
  - `conjecture_00000009617_false : ¬ Claim`; `_false_mod` covers every p ≥ 2;
    `_false_any_presentation` covers arbitrary presentations.
- **`X_c`.**
  - `ChargeShift` is the shift presented by `charge`.
  - `not_lang_of_bad`: `000` and `111` never occur.
  - `per_mem` and `lang_of_per`: the point `(1100)^∞` is in `X_c`, and so are all its factors.
  - `chargeMinor_det` gives `= 1`.
  - `charge_rank_ge` and `charge_rank_ge_mod` give rank ≥ r for every r ≤ 5.
  - `charge_counterexample`: the Fischer count exists, is ≤ 3, and the rank is ≥ 5.
  - `conjecture_00000009617_false_charge`, `_charge_mod` and `_charge_any_presentation`.
- **Not in Lean.**
  - the rank upper bounds;
  - `Fis(X_c) = 3` exactly;
  - the 6 follower sets of `X_c`, so the follower-set reading is not in Lean;
  - the Boolean and measure remarks.

  These are in the report and in `verify.py`.

The project has no `sorry`, no `native_decide`, and no added axioms. `#print axioms` shows only the
standard `propext`, `Classical.choice` and `Quot.sound`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想中有一条子句：sofic 移位的 Fisher（Fischer）最小状态数等于其语言 Hankel 矩阵的秩。按标准含义（域上的秩），这一条不成立。猜想是若干子句的合取，所以整个猜想为假。

**反例一：偶移位 X**（禁止块 `0 1^(2k+1) 0`）。

- Fischer 覆盖有 2 个状态：A-0->A，A-1->B，B-1->A。
- 任何至多 1 个顶点的图都不能呈现 X。
- Hankel 矩阵中，取行 11、0、01 和列 0、10、1，得到子式 [[1,1,1],[1,0,1],[0,1,1]]，其行列式为 −1。所以在任何域上秩恰为 3，不等于 2。

**反例二：电荷约束移位 X_c**（图为 0-1->1-1->2，2-0->1-0->0）。

- Fischer 状态数为 3，任意呈现也至少需要 3 个顶点。
- 非空 follower 集有 6 个，加上死状态共 7 个。
- Hankel 矩阵中，取行和列 ε、0、1、00、11，得到的 5×5 子式行列式为 1。又有行关系 1_F(ε)+1_F(001)=1_F(0)+1_F(1)，所以秩恰为 5。
- 5 与 3、6、7 都不相等，因此"follower 集个数"这种理解也被否定。

**说明。**

- 布尔秩（OR/AND 半环）总不超过 Fischer 状态数，小规模搜索中两者都相等，猜想在布尔秩的理解下可能成立。我们只否定域上秩的理解。
- 基于测度（隐 Markov 模型）的 Hankel 秩依赖于测度的选取，而猜想说的是"语言的 Hankel 矩阵"。

**Lean 项目**（Lean 4.19.0，仅用核心库）：

- 从定义出发形式化了移位、语言、图呈现、Fisher 最小状态数、Hankel 矩阵、行列式与秩。
- 对两个反例都证明了 `¬ Claim`（ℚ 上），以及对一切 p≥2（特别是一切素数 p）在 ℤ/p 上的版本。

**Python 脚本**用不同的方法独立验证了全部数值。
