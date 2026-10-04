# Disproof of conjecture 00000003952 (twin-width at most 1 vs distance-hereditary)

The conjecture is a conjunction. Its first clause says that **the graphs of twin-width at most 1
are exactly the distance-hereditary (DH) graphs**. This clause is false in both directions,
so the conjecture is false. The two complexity clauses (twin-width ≤ 2 is polynomial,
twin-width ≤ 3 is NP-hard) are not needed and not addressed.

| graph | edges | twin-width | DH? |
|---|---|---|---|
| house H = complement of P5 | 02, 03, 04, 13, 14, 24 | 1 | no |
| net N (triangle 0,1,2 with pendants 3,4,5) | 01, 12, 02, 03, 14, 25 | 2 | yes |

**House.** Contract {3,4}, then add 2, then 1, then 0. Every trigraph in this sequence has
maximum red degree ≤ 1; the values are 0, 1, 1, 1, 0. Twin-width 0 is impossible because H
has no twins.

H is not DH. The induced subgraph H − 0 = H[{1,2,3,4}] is the path 2-4-1-3, which is
connected. In it, d(2,3) = 3, but d_H(2,3) = 2 via 2-0-3.

**Net.** N is DH: every induced path is a shortest path. Every first contraction already gives
the new vertex red degree 2:

- Δ(0,1) = {3,4}
- Δ(0,3) = {1,2}
- Δ(0,4) = {2,3}
- Δ(3,4) = {0,1}

So tww(N) > 1. A width-2 sequence exists, so tww(N) = 2.

## Contents

- `report.tex`, `report.pdf`: the complete proof, definitions, the readings covered, and the
  Lean overview.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent Python 3 standard-library check. It uses:
  - trigraph simulation;
  - exact twin-width by exhaustive search over partition sequences;
  - DH tested three ways: BFS in all induced subgraphs, Bandelt–Mulder pruning, and forbidden
    induced subgraphs;
  - an enumeration of all connected graphs with at most 6 vertices, using `nauty-geng` if it
    is installed.

  On 5 vertices, the house and the gem are the only graphs with tww ≤ 1 that are not DH. On
  6 vertices, the net is the only DH graph with tww > 1.
- `verification.txt`: a fresh `lake build` log, the forbidden-token scan and the `verify.py`
  output.

## Lean

Everything is defined from scratch:

- graphs (edge lists on {0,…,n−1});
- trigraphs with none/black/red colours;
- `contract`, with the standard rule: black iff both parts are black-adjacent, none iff both
  are non-adjacent, red otherwise;
- contraction sequences, `seqWidth` (the maximum red degree over all trigraphs along the
  sequence), and `TwwLe G d` (some contraction sequence has width ≤ d);
- walks in induced subgraphs (`Reach`), connected induced subgraphs, and `DH` (every
  connected induced subgraph is isometric).

Main theorems:

- `house_tww_eq_one`, `house_not_DH`, `net_DH`, `net_tww_eq_two`
- `twwToDH_false : ¬ ClauseTwwToDH`
- `DHToTww_false : ¬ ClauseDHToTww`
- `conjecture_00000003952_false : ¬ Clause`, where
  `Clause := ∀ G, G.WF → (TwwLe G 1 ↔ DH G)`
- `conjecture_00000003952_conjunction_false (Rest) : ¬ (Clause ∧ Rest)`

The sanity checks `P5_twwLe_one` and `P5_DH` show that neither predicate is vacuous. The
DH property of the net is proved through a generic soundness theorem `dh_of_check`, which
holds for every well-formed graph, together with a kernel `decide`.

There is no `sorry`, no `native_decide` and no added axiom. `#print axioms` shows at most
`propext` and `Quot.sound`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

该猜想是三个命题的合取，其第一条为：“twin-width ≤ 1 的图恰为距离遗传图”。这一条在两个方向上都不成立，因此整个猜想不成立。
关于复杂度的两条（≤2 多项式可判定、≤3 NP-难）与本反证无关，本文不作讨论。

- **房子图 H**（P5 的补图，边 02,03,04,13,14,24）：twin-width 恰为 1，但不是距离遗传图。
  收缩序列为 {3,4}、2、1、0，每一步的最大红度依次为 0,1,1,1,0；H 没有孪生点，故 twin-width 不为 0。
  另一方面，导出子图 H−0 是路 2-4-1-3，它连通，其中 d(2,3)=3，而在 H 中 d(2,3)=2。
- **网图 N**（三角形 0,1,2，每个顶点挂一个悬挂点 3,4,5）：是距离遗传图（每条导出路都是最短路），
  但任何第一次收缩都会产生红度为 2 的顶点，故 twin-width 恰为 2。

Lean 4（仅核心库）从零定义了三元图（红黑图）、收缩、收缩序列、宽度、twin-width ≤ d、导出子图中的途径以及距离遗传性，
并证明了 `¬ Clause`。verify.py 用划分序列穷举与三种距离遗传判别方法独立复核。
