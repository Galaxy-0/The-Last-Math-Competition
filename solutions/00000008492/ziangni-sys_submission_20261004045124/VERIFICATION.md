# Verification

Verified 2026-10-04 UTC with Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

- Fresh project `lake build`: successful, 2166 targets, Main built from source.
- Direct `lake env lean -DwarningAsError=true Main.lean`: exit 0.
- Audited `system_ergodic`, `subadditive_process`, `expectation_X`, `mean_tendsto_zero`, `no_eventual_rate`, and `not_bigO`. Each depends only on `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, `native_decide`, or custom axiom declarations in the source. No auxiliary computation is required.
- Actual `Ergodic T μ` includes measure preservation and the invariant measurable-set condition. The probability measure is the unit Dirac mass on the full sigma-algebra of Unit.
- Actual Bochner integrals and real square roots are used; no expectation or convergence is asserted as a premise.
- The no-rate theorem quantifies over every real constant and starting index and produces a positive natural index. The final theorem negates the actual norm-based `Asymptotics.IsBigO` predicate.
- Built-in source editor opened and compiler attempted. The environment returned `Unable to find standard directories for platform`. Tectonic successfully compiled the actual PDF; final compilation had no overfull or underfull TeX box warnings.
- Both final PDF pages were independently rendered at 1500 pixels with Poppler and visually inspected. No clipping, overlaps, missing glyphs or problematic spacing remained.
- Git diff whitespace checks passed. Only this personal submission is committed; dependency junctions and build products are ignored.

## Original and eligibility

English: Definition: The ergodicization of Fekete's lemma: the one-sided approximation rate of mean convergence of random subadditive sequences. Conjecture: The universal spectrum of convergence rates is dominated by log n/n (a logarithmic harmonic spectrum law); the slowest converging systems are explicitly constructed from low-complexity sequences of Sturmian and Thue-Morse type (a low-complexity construction law); and the approximation lower bound of the construction matches the upper bound (a matching law). (Fekete Sturmian Thue-Morse matching rates)

中文：定义：Fekete 引理的遍历化：随机次可加序列的均值收敛的单侧逼近速率。猜想：收敛速率的普适谱由 log n/n 主导（对数调和谱律）；且最慢收敛系统由 Sturmian 与 Thue–Morse 型低复杂度序列显式构造（低复杂度构造律）；构造的逼近下界与上界匹配（匹配律）。

At selection, metadata marked the ID unsolved and HEAD had no solution files for this ID. The live all-state upstream PR search for `00000008492` returned `[]` at selection and again before final packaging. Parent coordination reserved the ID for job32. The universal rate clause has no uniform boundedness requirement on the unnormalized sequence. The report explicitly identifies the growth of the chosen process and the exact disproof scope.
