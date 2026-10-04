# Proof of conjecture 00000000035

**Conjecture:** there exists `N` such that every 2-coloring of `[N] = {1, …, N}`
contains a monochromatic Schur triple `(x, y, z)`, `x + y = z`, with `xy + 1`
prime.

**Answer: true, with `N = 17`**, even when `x < y` is required. For `x < y`
this is optimal: the coloring `0010101110110101` of `[16]` avoids every such
triple. (If `x = y` is also allowed, `N = 7` already works.) The `k` in `N(k)`
appears nowhere else in the statement, and `N = 17` works for every `k`. If `N(k)` was meant as a
k-color Schur number, with "2-coloring" a typo for "k-coloring", that would be a different and much
harder statement. This submission does not claim it: it proves the conjecture as written in both
languages, for 2-colorings.

The proof is a finite case analysis on the 31 triples `x < y`,
`x + y ≤ 17`, `xy + 1` prime. A DPLL refutation tree with 11 branchings and
12 leaves shows that no 2-coloring of `[17]` avoids all of them. The report
lists every branch, and each deduction is justified by a named triple.

## Contents

- `report.tex`, `report.pdf`: the complete proof, including the whole case tree.
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py`: an independent exhaustive check over all `2^17` colorings (Python 3 standard library).
- `verification.txt`: the build log, axiom audit and Python output.

## Lean

- `Prime` is the standard definition. A verified trial-division checker decides it
  (`prime_of_check`, `check_of_prime`).
- `schur_17`: every `c : Nat → Bool` has a monochromatic `SchurPrimeTriple 17 x y z`
  (`1 ≤ x < y`, `x + y = z ≤ 17`, `Prime (x*y+1)`).
- `conjecture_00000000035 : ∀ k, ∃ N, ∀ c, ∃ x y z, SchurPrimeTriple N x y z ∧ c x = c y ∧ c y = c z`.
- `conjecture_00000000035_le` is the variant that only requires `x ≤ y`.
- `conjecture_00000000035_on_interval`: the same statement with colorings defined only on `[N]`.
- `sixteen_avoids`: an explicit coloring of `[16]` with no such triple.

The project has no `sorry`, no `native_decide`, and no added axioms.
`#print axioms` shows at most `propext`, `Classical.choice` and `Quot.sound`.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想：存在 `N`，使 `[N]` 的任意 2-染色都含有单色 Schur 三元组 `x+y=z`，且 `xy+1` 为素数。
我们证明 `N=17` 成立，并且即使要求 `x<y` 也成立。在 `x<y` 的要求下 17 是最优的：
`[16]` 的染色 `0010101110110101` 不含此类三元组。若允许 `x=y`，`N=7` 就已足够。
证明是对 31 个三元组做有限分类讨论，共 11 次分支、12 个叶子。
Lean 完整检查了这一证明，Python 也对全部 `2^17` 种染色做了穷举验证。
