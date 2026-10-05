# Counterexample to conjecture 00000007964

Among other things, the conjecture claims that **binary linear quasi-perfect codes of length `n`
exist if and only if `n = 2^k − 1` or `n` lies in a finite exceptional list** (the "Levenshtein set").
The conjecture is a conjunction, so refuting this clause refutes it. Its first conjunct, the
"gap constant of the radius spectrum", is never defined. We do not address it, and the disproof
does not need it.

**Which notion of quasi-perfect.** The conjecture defines a *stronger* notion than the textbook one.
Its preamble asks for covering radius `r + 1` (with `r = e`, the packing radius) **and** a "tight
uniform shell distribution". We treat both readings:

1. **Standard:** covering radius `ρ = e + 1`, where `e = ⌊(d−1)/2⌋`.
2. **The conjecture's uniform-shell notion:** `ρ = e + 1`, and the code is *shell-uniform*. That is,
   any two words at the same distance from the code have equally many codewords at distance `j`,
   for every `j`. This constrains every shell, which is the strongest reasonable form.

Under **both** readings, such codes exist for exactly the lengths `n ≥ 2`. So the clause is false.

**Code families.**

- **Shortened Hamming codes `SH(n)`** (`d = 3`). Take parity-check columns equal to the binary
  expansions of `1, …, n`. For every `n ≥ 3` with `n + 1` not a power of 2, this code has `d = 3`,
  `e = 1` and covering radius `2`.
- **Once-shortened Hamming codes `SH(2^m − 2)`, `m ≥ 3`.** These are also shell-uniform. The linear
  maps fixing the all-ones syndrome act transitively on the weight-1 cosets.
- **Extended Hamming codes** of length `2^m`, `m ≥ 2` (`d = 4`, covering radius `2`). These are
  shell-uniform because the affine group `AGL(m,2)` acts transitively on the cosets of each minimum
  weight.
- **Even-weight codes** of every length `n ≥ 2` (`d = 2`, covering radius `1`). These are
  shell-uniform via the explicit bijection `c ↦ c ⊕ x ⊕ y`.
- No length `n ≤ 1` works.

Take any finite list `L` and choose an even `n > max L` with `n ≥ 4`. Then `n + 1` is odd and
`≥ 5`, so `n` is not of the form `2^k − 1`, and `n ∉ L`. Yet `SH(n)` (d = 3) and `EW(n)`
(shell-uniform) are quasi-perfect codes of length `n`.

**Readings covered.**

- Both the strict reading `ρ = e + 1` and the non-strict reading `ρ ≤ e + 1`.
- The uniform-shell notion.
- Counting only codes with `d ≥ 3` or `d ≥ 4`, so the disproof does not rely on trivial codes. Under
  the uniform-shell reading, this holds on paper and in `verify.py`, using `SH(2^m − 2)` and
  extended Hamming codes.
- `k` unrestricted, since only the "only if" direction is used.
- Any finite list `L`.
- "Tight" read as "nearly perfect" (Goethals–Snover: meeting the Johnson bound `|C| ≤ 2^n/(n+2)` for
  e = 1, n even). `SH(2^m − 2)` has exactly `2^n/(n+2)` codewords, so it is nearly perfect at infinitely many
  lengths `2^m − 2`. This is on paper only.

## Contents

- `report.tex`, `report.pdf`: the complete mathematical report.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent brute-force check using only the Python 3 standard library.
  - Codewords are listed explicitly, and covering radii come from a BFS on the hypercube.
  - Shell uniformity is checked through coset weight distributions grouped by minimum weight.
  - It also enumerates all 29212 binary linear codes of length 7, and all shorter ones.
- `verification.txt`: the fresh build log, the forbidden-token scan and the Python output.

## Lean

Words are `List Bool`, and codes are predicates `List Bool → Prop`. The definitions are:

- `IsLinear n C`: an F₂-subspace of F₂ⁿ.
- `MinDist C d` and `CovRad n C r`: the attained minimum distance and covering radius, proved
  unique by `minDist_unique` and `covRad_unique`.
- `IsQP n C`: linear, and the covering radius is `(d−1)/2 + 1`. `QPLen n` means such a code of
  length `n` exists.
- `DistTo C x r`: `r` is the distance from `x` to `C`.
- `ShellUniform n C`: for any `x`, `y` of length `n` at the same distance from `C` and any `j`,
  there are maps `f`, `g` between their `j`-shells with `g ∘ f = id` and `f ∘ g = id`.
  `UQPLen n := ∃ C, IsQP n C ∧ ShellUniform n C`.

The theorems are:

- `SH_quasiPerfect`: for all `n ≥ 3` with `n+1 ≠ 2^k`, `SH n` has `MinDist 3` and `CovRad 2`.
- `EH_quasiPerfect`: for all `m ≥ 2`, the extended Hamming code has `MinDist 4` and `CovRad 2`.
- `EW_quasiPerfect`: for all `n ≥ 2`, the even-weight code is quasi-perfect.
- `hamming_not_QP`: the Hamming codes are perfect, so they are not quasi-perfect. This is a
  non-vacuity check.
- `QP_spectrum : QPLen n ↔ 2 ≤ n`.
- `conjecture_00000007964_false : ¬ LevenshteinClause`, where
  `LevenshteinClause := ∃ L : List Nat, ∀ n, QPLen n ↔ ((∃ k, n + 1 = 2^k) ∨ n ∈ L)`.
- `onlyIf3_false`, `onlyIf4_false`, `onlyIf_any_false`, `onlyIfWeak_false` and
  `levenshteinAtLeast_false`: even the "only if" direction fails. It still fails when only codes
  with `d ≥ 3` or `d ≥ 4` count, and when perfect codes are allowed.
- Uniform-shell notion:
  - `EW_shellUniform`, for all `n`.
  - `SH5_not_shellUniform`: `ShellUniform` is a genuine restriction.
  - `UQP_spectrum : UQPLen n ↔ 2 ≤ n`.
  - `onlyIfUniform_false`.
  - `conjecture_00000007964_false_uniform : ¬ LevenshteinClauseUniform`, which is the iff clause
    with `UQPLen`.

**Not in Lean.** These are proved in the report and checked by `verify.py`:

- the shell uniformity of the extended Hamming codes and of `SH(2^m − 2)`, so the `d ≥ 3` and
  `d ≥ 4` versions of the uniform-shell refutation are on paper and in `verify.py` only;
- the explicit shell counts;
- the repetition codes;
- the dimension formula.

The project has no `sorry`, no `native_decide` and no added axioms. `#print axioms` shows at most
`propext`, `Classical.choice` and `Quot.sound`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py      # about one minute
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想的第二部分断言：二元线性 quasi-perfect 码在长度 `n` 存在，当且仅当 `n = 2^k − 1` 或 `n` 属于某个有限例外列表。该断言是错误的。猜想是合取命题，所以否定这一部分即否定整个猜想。第一部分的“间隙常数”没有给出定义，本文不讨论，否定也不依赖它。

猜想本身的定义比教科书定义更强：要求覆盖半径为 `e+1`（`e` 为填充半径），并且具有“紧壳均匀分布”。我们处理两种解读：

1. 标准解读：`ρ = e + 1`。
2. 猜想自己的“壳层均匀”解读：此外，到码距离相同的任意两个字，在每个半径 `j` 的壳层中码字个数相同（最强形式）。

在两种解读下，这类码都恰好存在于所有长度 `n ≥ 2`。

- 缩短 Hamming 码：对每个 `n ≥ 3` 且 `n+1` 不是 2 的幂，`d = 3`，覆盖半径 `2`。其中长度 `2^m − 2` 的码还满足壳层均匀。
- 扩展 Hamming 码：长度 `2^m`，`d = 4`，壳层均匀。
- 偶重码：对每个 `n ≥ 2` 均为壳层均匀的 quasi-perfect 码。

Lean 4（仅核心库）从零定义了线性码、最小距离、覆盖半径、quasi-perfect 以及壳层均匀 `ShellUniform`（以显式双射表述），并证明了：

- 长度谱 `QP_spectrum`、`UQP_spectrum`（都是 `↔ 2 ≤ n`）；
- 主定理 `conjecture_00000007964_false` 与 `conjecture_00000007964_false_uniform`；
- `SH5_not_shellUniform`，说明壳层均匀条件确实是实质性的限制。

扩展 Hamming 码和 `SH(2^m−2)` 的壳层均匀性未在 Lean 中形式化，由报告给出证明（仿射群在每种最小重量的陪集上可迁），并由 `verify.py` 检验。
