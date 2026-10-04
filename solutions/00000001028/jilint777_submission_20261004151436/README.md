# Disproof of conjecture 00000001028 (Kirkman quadruple systems below 316)

The conjecture states two things. KQS(v) (resolvable S(2,4,v) designs) exist for all
v ≡ 4 (mod 12) with v ≥ v₀ = 316, and **below v₀ there are exactly 21 exceptional values**.
The second clause is false, so the conjecture is false whatever the truth of the first clause.

Only **26** values v ≡ 4 (mod 12) lie below 316 (4, 16, …, 304). We give explicit Kirkman
quadruple systems for **seven** of them, verified in Lean:

| v | construction | classes | blocks |
|---|---|---|---|
| 4 | a single block | 1 | 1 |
| 16 | lines of AG(2,4) | 5 | 20 |
| 28 | Hermitian unital U(3) in PG(2,9), resolved by computer search | 9 | 63 |
| 40 | lines of PG(3,3), packed into 13 spreads | 13 | 130 |
| 52 | 1-rotational over Z₅₁ ∪ {∞}, base blocks {1,2,20,24}, {4,25,12,49}, {5,10,45,30}, {6,9,48,50} | 17 | 221 |
| 64 | lines of AG(3,4) | 21 | 336 |
| 76 | 1-rotational over Z₇₅ ∪ {∞}, base blocks {1,34,47,48}, {2,33,67,69}, {3,56,7,71}, {4,61,13,16}, {5,60,37,43}, {14,65,70,49} | 25 | 475 |

So at most 26 − 7 = **19** admissible values below 316 can be exceptional, never 21.

The same holds under the other readings:

- If "below v₀" includes 316 itself, at most 20 values can be exceptional.
- If trivial orders such as v = 4 are excluded, the set only gets smaller.
- If "exceptional" counts every v < 316 regardless of residue, at least 288 values have no
  KQS, because a KQS(v) with v ≥ 2 needs v ≡ 4 (mod 12). This last reading is covered in
  the report only.

The true count is 0: Hanani, Ray-Chaudhuri and Wilson (1972) showed that KQS(v) exists for
every v ≡ 4 (mod 12). The disproof does not use this result.

## Contents

- `report.tex`, `report.pdf`: the complete argument. It contains the explicit resolutions for
  v = 28 and 40, the proof of the 1-rotational construction, and the counting argument.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py` (Python 3 standard library) checks the seven designs read from `Main.lean` by
  pair counting, which is a different method from the Lean checker. It also re-derives each design
  from its geometric or algebraic description and recounts the bound.
- `verification.txt`: a fresh `lake build` log, the forbidden-token scan and the `verify.py`
  output.

## Lean

- `IsKQS v R` states the definition literally. Every block is a duplicate-free 4-element list
  of points `< v`. In every parallel class, each point lies in exactly one block (by `countP`).
  Every pair of distinct points lies in exactly one block. `HasKQS v := ∃ R, IsKQS v R`.
- `check v R` is a fast bitmask checker. `check_sound : check v R = true → IsKQS v R` is proved
  in general. `kqs_4`, …, `kqs_76` verify the seven explicit resolutions `R4`, …, `R76` by
  kernel evaluation (`decide +kernel`).
- `Exceptional v := v % 12 = 4 ∧ v < 316 ∧ ¬ HasKQS v`. `ExactlyExceptional k` says that the
  exceptional values are exactly the entries of a duplicate-free list of length `k`.
  `Clause2 := ExactlyExceptional 21` and `Conjecture := Clause1 ∧ Clause2`.
- Main results:
  - `exceptional_le_19`: at most 19 exceptional values.
  - `clause2_false : ¬ Clause2`.
  - `conjecture_00000001028_false : ¬ Conjecture`.
  - `clause2_le_false`: the non-strict reading `v ≤ 316`, where at most 20 values can be
    exceptional.
- Non-vacuity:
  - `not_hasKQS_two_three` and `not_hasKQS_five`: there is no KQS on 2, 3 or 5 points, so
    `HasKQS` is not trivially true. For v = 5 a block fits, but no parallel class can split 5
    points into 4-sets.
  - `exceptional_iff`: for admissible `v < 316`, `Exceptional v ↔ ¬ HasKQS v`.
  - `admissible_below_316`: the 26 admissible values.

The project has no `sorry`, no `native_decide` and no added axioms. `#print axioms` shows at
most `propext`, `Classical.choice` and `Quot.sound`. The build takes about one minute.

Only the explicit designs are in Lean. The geometric explanations of where they come from,
and the necessary condition v ≡ 4 (mod 12), are proved in the report and checked by
`verify.py`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想包含两部分：对一切 v ≡ 4 (mod 12) 且 v ≥ v₀ = 316，Kirkman 四元系 KQS(v)（可分解的 S(2,4,v)）都存在；并且在 v₀ 以下恰有 21 个例外值。
第二部分是错的，因此无论第一部分是否成立，整个猜想都不成立。

316 以下满足 v ≡ 4 (mod 12) 的值只有 26 个（4, 16, …, 304）。我们对其中 7 个值 v = 4, 16, 28, 40, 52, 64, 76 给出了显式的 KQS：
- v = 4：单个区组；
- v = 16 与 v = 64：AG(2,4) 与 AG(3,4) 的直线；
- v = 28：PG(2,9) 中 Hermitian 酉空间 U(3) 的一个可分解；
- v = 40：PG(3,3) 的直线划分为 13 个 spread（packing）；
- v = 52 与 v = 76：Z₅₁ ∪ {∞} 与 Z₇₅ ∪ {∞} 上的 1-旋转构造。

所以 316 以下最多 19 个例外值。即使把 316 本身也算进来，最多也只有 20 个，不可能恰为 21。
若"例外值"指不论模 12 余数、一切没有 KQS 的 v < 316，则至少有 288 个，同样不是 21。
（事实上，Hanani、Ray-Chaudhuri 与 Wilson 于 1972 年证明了对一切 v ≡ 4 (mod 12) 都存在 KQS(v)，即根本没有例外值；本证明不依赖该结果。）

Lean 4（仅核心库）中的形式化：
- 按定义刻画 KQS：区组为 4 元集，每个平行类划分点集，每对不同点恰在一个区组中；
- 用经过证明可靠的位掩码检验器（`check_sound`），在内核中验证这七个设计；
- 证明 `conjecture_00000001028_false : ¬ Conjecture`，以及非严格读法下的 `clause2_le_false`。

`verify.py` 只用 Python 标准库，以不同于 Lean 的方法独立复核全部设计及计数。
