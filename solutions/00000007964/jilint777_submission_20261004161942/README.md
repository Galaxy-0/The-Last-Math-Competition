# Counterexample to conjecture 00000007964

Among other things, the conjecture claims that **binary linear quasi-perfect codes of length `n`
exist if and only if `n = 2^k − 1` or `n` lies in a finite exceptional list** (the "Levenshtein set").
The conjecture is a conjunction, so refuting this clause refutes it. Its other conjunct, the
"gap constant of the radius spectrum", is never defined and is not discussed here.

A code is quasi-perfect when its covering radius is one more than its packing radius:
`ρ = e + 1` with `e = ⌊(d−1)/2⌋`. This is the standard definition, written in the conjecture as
"covering radius r+1". The clause is false because quasi-perfect codes exist for **every** length
`n ≥ 2`:

- **Shortened Hamming codes** (`d = 3`). Take parity-check columns equal to the binary expansions
  of `1, …, n`. For every `n ≥ 3` with `n + 1` not a power of 2, this code has `d = 3`, `e = 1` and
  covering radius `2`. Write `2^k ≤ n < 2^(k+1)`. Every syndrome `s < 2^(k+1)` is `0`, a single
  column, or the sum of the two columns `2^k` and `s ⊕ 2^k`. The syndrome `2^(k+1) − 1 > n` is not
  `0` and not a single column.
- **Extended Hamming codes** of length `2^m`, `m ≥ 2` (`d = 4`, covering radius `2`). These have
  uniform shells: a word at distance 2 from the code has exactly `2^(m−1)` codewords at distance 2,
  and a word at distance 1 has exactly 1 codeword at distance 1.
- **Even-weight codes** of every length `n ≥ 2` (`d = 2`, `e = 0`, covering radius `1`). Each
  odd-weight word has exactly `n` codewords at distance 1.
- No length `n ≤ 1` works, so the spectrum is exactly `{n ≥ 2}`.

Take any finite list `L` and choose an even `n > max L` with `n ≥ 4`. Then `n + 1` is odd and
`≥ 5`, so `n` is not of the form `2^k − 1`, and `n ∉ L`. Still, `SH(n)` is quasi-perfect with `d = 3`.

**Readings covered.** The disproof refutes the strict reading `ρ = e + 1` and the non-strict reading
`ρ ≤ e + 1`. It also refutes the versions that count only codes with `d ≥ 3` or `d ≥ 4`, so it does
not rely on "trivial codes". Only the "only if" direction is needed, with `k` unrestricted, so every
restriction on `k` is covered too. `L` can be any finite list. Under the "relaxed, uniform shell"
reading in the preamble, the extended Hamming and even-weight families still apply. Both are
infinite and lie outside `{2^k − 1}`. Shortened Hamming codes are generally not uniformly packed,
so this reading relies on those two families.

## Contents

- `report.tex`, `report.pdf`: the complete mathematical report.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent brute-force check using only the Python 3 standard library. It lists
  codewords explicitly and gets covering radii from a BFS on the hypercube. It also enumerates all
  29212 binary linear codes of length 7, and all shorter ones.
- `verification.txt`: the fresh build log, the forbidden-token scan and the Python output.

## Lean

Words are `List Bool`, and codes are predicates `List Bool → Prop`. The definitions are:

- `IsLinear n C`: an F₂-subspace of F₂ⁿ.
- `MinDist C d` and `CovRad n C r`: the attained minimum distance and covering radius, proved
  unique by `minDist_unique` and `covRad_unique`.
- `IsQP n C`: linear, and the covering radius is `(d−1)/2 + 1`.

The theorems are:

- `SH_quasiPerfect`: for all `n ≥ 3` with `n+1 ≠ 2^k`, the shortened Hamming code `SH n` is linear
  with `MinDist 3` and `CovRad 2`.
- `EH_quasiPerfect`: for all `m ≥ 2`, the extended Hamming code is linear with `MinDist 4` and
  `CovRad 2`.
- `EW_quasiPerfect`: for all `n ≥ 2`, the even-weight code is quasi-perfect.
- `hamming_not_QP`: the Hamming codes of length `2^m − 1` (`m ≥ 3`) are perfect, so they are
  **not** quasi-perfect. This is a non-vacuity check.
- `QP_spectrum : QPLen n ↔ 2 ≤ n`.
- `conjecture_00000007964_false : ¬ LevenshteinClause`, where
  `LevenshteinClause := ∃ L : List Nat, ∀ n, QPLen n ↔ ((∃ k, n + 1 = 2^k) ∨ n ∈ L)`.
- `onlyIf3_false`, `onlyIf4_false`, `onlyIfWeak_false` and `levenshteinAtLeast_false`: even the
  "only if" direction fails. It still fails when only codes with `d ≥ 3` or `d ≥ 4` count, and when
  perfect codes are allowed.

**Not in Lean.** The shell-count (uniform packing) statements, the repetition codes and the
dimension formula are not formalized. The report proves them and `verify.py` checks them.

The project has no `sorry`, no `native_decide` and no added axioms. `#print axioms` shows at most
`propext`, `Classical.choice` and `Quot.sound`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py      # about one minute
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想的第二部分断言：二元线性 quasi-perfect 码（覆盖半径 = 填充半径 `e = ⌊(d−1)/2⌋` 加 1）在长度 `n`
存在，当且仅当 `n = 2^k − 1` 或 `n` 属于某个有限例外列表。该断言是错误的。猜想是合取命题，所以否定这一部分即否定整个猜想。第一部分的“间隙常数”没有给出定义，本文不讨论。

- **缩短 Hamming 码**：校验矩阵的列取 `1, …, n` 的二进制表示。对每个 `n ≥ 3` 且 `n+1` 不是 2 的幂，
  该码满足 `d = 3`、`e = 1`、覆盖半径 `2`，因此是 quasi-perfect 码。
- **扩展 Hamming 码**：长度 `2^m`（`m ≥ 2`），`d = 4`，覆盖半径 `2`，且壳层分布完全均匀。
- **偶重码**：对每个长度 `n ≥ 2`，`d = 2`，覆盖半径 `1`。
- 长度 `n ≤ 1` 不存在这样的码。因此 quasi-perfect 码的长度谱恰为 `{n ≥ 2}`。

对任意有限列表 `L`，取偶数 `n > max L` 且 `n ≥ 4`。此时 `n+1` 是奇数且不是 2 的幂，`n ∉ L`，
但 `SH(n)` 是 `d = 3` 的 quasi-perfect 码，矛盾。

覆盖的解读：严格解读（`ρ = e+1`）与非严格解读（`ρ ≤ e+1`）；只计 `d ≥ 3` 或 `d ≥ 4` 的码；`k` 的任意取值范围；任意有限例外集。
按“松弛（均匀壳层）”的解读，扩展 Hamming 码与偶重码两个无穷族仍构成反例。

Lean 4（仅核心库）从零定义了线性码、最小距离、覆盖半径和 quasi-perfect，并证明了上述三个族、长度谱 `QPLen n ↔ 2 ≤ n`，
以及主定理 `conjecture_00000007964_false : ¬ LevenshteinClause`。壳层计数、重复码和维数公式未在 Lean 中形式化，
由报告给出证明，并由 `verify.py` 检验。
