# Verification

Verified 2026-10-04 UTC with Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

- Fresh project `lake build`: success, 2164 targets, Main built from source.
- Direct `lake env lean Main.lean -DwarningAsError=true`: exit 0.
- Six audits (`system_ergodic`, `driver_unbounded`, `optimal_attained`, `optimal_formula`, `ratio_tendsto_half`, `not_sublinear`) use only `[propext, Classical.choice, Quot.sound]`.
- Source scan: no `sorry`, `admit`, `native_decide` or custom axiom declarations.
- Actual mathematical objects: Unit compact space, identity continuous map, constant continuous observable, Dirac probability measure, actual Ergodic condition including measure preservation, actual driving sequence, finite sums and iterates, genuine sSup of the entire range, filter limit and Asymptotics.IsLittleO negation.
- The supremum value is derived from a proved singleton range; the arithmetic expression is not assumed. Every positive n and every fixed window origin are covered. No auxiliary computation is needed.
- Native source editor opened and compiler attempted; environment error: `Unable to find standard directories for platform`. Actual Tectonic compilation succeeded with no TeX box warnings.
- Both complete final PDF pages rendered at 1500 pixels using Poppler and visually inspected: clean margins, legible formulas and prose, no clipping, overlaps or missing glyphs.
- Scoped Git whitespace checks passed. Public dependency pins retained; local caches and junctions ignored. No shared dependency cache writes or lake clean were performed.

## Original scope and eligibility

English: Definition: Nonautonomous ergodic optimization: the supremum of sliding averages sup (1/n) sum (f(T^i x) + h_i) under a driving sequence h_n. Conjecture: The supremum under bounded driving is uniformly bounded by an explicit linear expression in the driving amplitude (an amplitude linear law); under unbounded driving the growth of the supremum is sublinear (a sublinear law); and the correction under random driving is a diffusion constant (a diffusion correction law), with variance increment half the driving variance (a half-variance law). (nonautonomous bounded sublinear diffusion correction)

中文：定义：非自治遍历优化：驱动序列 h_n 下的滑动平均 sup (1/n)Σ(f(T^i x)+h_i) 的上确界。猜想：有界驱动的上确界一致有界且界为驱动幅度的显式线性式（幅度线性律）；无界驱动下上确界的增长为亚线性（亚线性律）；随机驱动的修正为扩散常数（扩散修正律），修正的方差增量为驱动方差的一半（半方差律）。

Both originals read. The universal unbounded-driver sublinear clause has no restriction excluding linear nonnegative driving. The actual finite-window supremum over initial states is computed. The additional origin parameter is fixed before the n-limit, and is not optimized over all possible starting times.

Eligibility used exact upstream `The-Last-Math-Competition/The-Last-Math-Competition`. The successful all-state inventory with limit 1000 included both titles and bodies; local exact 11-digit and short-ID scans found no matches. Successful direct all-state search for `00000008480` returned `[]`. Metadata marked unsolved and HEAD had no solution paths for the ID. Full inventory is retained in `work/overnight/37-scratch/all-prs.json`. Root approved and reserved the candidate before completion.
