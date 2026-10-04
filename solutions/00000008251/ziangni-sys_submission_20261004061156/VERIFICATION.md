# Verification

Verified 2026-10-04 UTC with Lean 4.19.0 and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

- Fresh project `lake build`: success, 2804 targets; Main built from source.
- Direct complete source `lake env lean Main.lean -DwarningAsError=true`: exit zero.
- Seven audits (`complete_market`, `no_arbitrage`, `expectation_eq_weight`, `martingale_unique`, `equivalent_martingale_unique`, `extreme_count`, `count_formula_fails`) use only propext, Classical.choice and Quot.sound.
- No sorry, admit, custom axioms or native_decide in the proof source. No auxiliary computations are used.
- The actual state space is Fin 2 with the discrete Borel measurable structure. The reference is a normalized sum of actual scaled Dirac measures. Both singleton masses are proved positive.
- The actual Arrow-security payoff matrix is identified with I₂ and Matrix.rank is computed as two. All contingent claims are replicated by genuine portfolio sums; a constant numeraire is replicated and no-arbitrage is proved.
- Martingale probability means both one-period discounted expectation equations with trivial initial information. The equations use actual Bochner integrals. Indicator integration computes them; countable-measure extensionality proves that every solution is the actual reference probability.
- Both genuine absolute-continuity directions are included for equivalent martingale measures. Their full set is also a singleton. The finite mass-coordinate image is defined using all actual qualifying probability measures, not an assumed weight table. Mathlib extremePoints and Set.ncard then compute the count one, compared with actual state cardinality minus actual matrix rank zero.
- Tectonic compiled the final two-page PDF without TeX box warnings. Both pages were rendered at 1500 pixels and fully visually inspected: legible text, complete formulas and proof, clean margins, no clipping, overlaps or missing glyphs.
- The saved-source editor was opened and native compiler attempted; its environment error was `Unable to find standard directories for platform`. The delivered PDF was successfully built with Tectonic.
- Public Git pins retained; local caches and junctions ignored. A coordinated targeted Matrix.Rank cache extension downloaded three files; no dependency revision changed and no lake clean was run. Scoped Git whitespace checks passed.

## Source and scope

English: Definition: The distance between no-arbitrage and equivalent martingale measures in financial markets: the information distance inf_mart of the set M of martingale measures of a market (Omega, F, prices S). Conjecture: inf_mart (the minimal f-divergence of martingale measures) is a measure of market incompleteness (an incompleteness measure law); the number of extremal points of the set of martingale measures of a finite-state market is the cardinality of Omega minus the rank of the assets (an extremal count formula); and the explicit form of optimal replication in incomplete markets (quadratic error) is the density ratio of the minimal-entropy martingale measure (a minimal-entropy replication duality law).

中文：定义：金融市场无套利与等价鞅测度的距离：市场（Ω, F, 价格 S）的鞅测度集 M 的信息距离 inf_mart。猜想：inf_mart（鞅测度的最小 f-散度）为市场不完备的度量（不完备度量律）；且有限状态市场的鞅测度集的极值点数为 Ω 的基数-资产的秩（极点计数公式）；不完备市场的最优复制（二次误差）的显式为鞅测度的最小熵测度的密度比（最小熵-复制对偶律）。

Both originals were read. The extreme-point formula is stated for finite-state markets without an incompleteness restriction. The separate replication assertion refers to incomplete markets and is not used here. Either all martingale probabilities or only equivalent martingale probabilities gives the same counterexample. The actual matrix rank is the dimension of the payoff range, and the Arrow securities avoid any ambiguity about including a separately named bond. The singleton's affine dimension is zero, but its extreme-point count is one. Only the count conjunct is refuted.

## Eligibility

Exact upstream `The-Last-Math-Competition/The-Last-Math-Competition`: successful full all-state title/body inventory with limit 1000 returned 412 records. Local exact-ID and short-ID scans found no match. Successful direct all-state search returned an empty list. Metadata marked proven=false and disproven=false; the HEAD solution tree was empty for this ID. Current claims were checked and root approved/reserved job46. Inventory retained in `work/overnight/46-scratch/all-prs.json`. Failed commands were not treated as empty evidence.
