# Solution Review — Conjecture 00000002594 (PR 348)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "the direct product of two LYM posets retains the LYM property, and the permutation structure of normalized matchings is the braiding of local matchings of the factors; the braiding has genus zero."
- LaTeX: compiled (pdflatex twice, exit 0, 1 page); shipped main.pdf real PDF v1.5 matching recompiled text (kerning-only differences).
- Lean build: exit 0, fresh (`rm -rf .lake && lake build`), Lean 4.19.0, `import Std` + `Std.Internal.Rat`. `set_option maxHeartbeats/maxRecDepth` raised (allowed). Only `#print axioms` info lines.
- Forbidden content: none (grep zero matches). Axioms: [propext, Quot.sound, Classical.choice] only — standard.
- Auxiliary code: no Python/JS shipped; recorded logs match my fresh build. Independent python3 brute force: P (rank sizes [1,1,3]) max Lubell over ALL antichains = 1.0; Q (2-chain) = 1.0 (both LYM); P×Q rank sizes [1,2,4,3]; max Lubell over ALL 2^10-antichain space = 1.25 attained exactly at A = {(a,1),(c,0),(d,0),(e,0)}; A is an antichain and a MAXIMAL antichain (every outside element comparable to a member). Fully confirms the submission.
## Semantic audit
Conjecture (literal): the direct product of two LYM posets retains the LYM property (plus further braiding/genus claims). The PR disproves the multiplicative-closure clause with P = ordinal sum of antichains of sizes (1,1,3) and Q = the 2-chain.

Key Lean signatures (lean/Main.lean, namespace Conjecture2594):
- `structure RankedPoset V` — vertices list with `nodup`, `complete`, `refl/antisymm/trans` for the order, `rank`, `height`, `rank_bound`, `minimal_rank` (minimal elements have rank 0), `maximal_rank` (maximal elements have rank = height), `cover_rank : Cover le x y → rank y = rank x + 1` — a genuine finite graded poset formalization (not a bare relation).
- `def P : RankedPoset (Fin 5)` with `pRank = [0,1,2,2,2]`, `pLE x y := x = y ∨ pRank x < pRank y` (all instances by kernel decide); `def Q : RankedPoset (Fin 2)` the 2-chain; `def R : RankedPoset (Fin 5 × Fin 2)` with `productLE x y := P.le x.1 y.1 && Q.le x.2 y.2`, `rank x = P.rank x.1 + Q.rank x.2`, `height = 3`; `theorem product_order`, `theorem product_rank` identify R with the standard ranked direct product.
- `def lubell` — exact rational sum Σ_{x∈S} 1/|rank level of x| via Std.Internal.Rat; `def LYM P := ∀ S : V → Bool, Antichain P S → lubell P S ≤ 1`; `theorem every_subset_represented` + `theorem lym_for_every_subset` bridge arbitrary Prop-valued subsets, so quantification over Boolean characteristic functions omits nothing.
- `theorem checked_P` (all 32 subsets, with `tuple5_eta`), `theorem P_is_LYM`, `theorem checked_Q`, `theorem Q_is_LYM` — both factors LYM, exhaustively.
- `def witness` = {(0,top),(2,0),(3,0),(4,0)}; `theorem witness_antichain`, `theorem factor_rank_sizes` ([1,1,3] and [1,1]), `theorem product_rank_sizes` ([1,2,4,3]), `theorem witness_lubell : lubell R witness = 5/4`, `theorem witness_exceeds_one`.
- `theorem product_not_LYM : ¬LYM R`, and the final `theorem conjecture2594_false : ¬(LYM P → LYM Q → LYM R)` — negation of a necessary instance of the claimed universal product law.

My independent brute force reproduces everything: both factors are LYM; the product's rank sizes are [1,2,4,3]; the maximal Lubell value over all antichains of P×Q is exactly 5/4 at precisely the submitted witness, which is moreover a maximal antichain (so the conjecture's "maximal antichains" wording does not dodge it). The witness's Lubell sum 1/2 + 3/4 = 5/4 > 1 is also verified by hand. This is a genuine counterexample to multiplicative closure of LYM posets — the further braiding/genus-zero clauses fall with the conjunction. Not vacuous: real ranked posets, real product, real rational Lubell sums, exhaustive antichain quantification.
## Issues found
- none blocking. (For the record I checked whether a classical positive product theorem would conflict: products of chains/Peck/regular posets are the classical closure results; general LYM posets are not closed under products, and this counterexample — verified independently — settles it.)
## Verdict rationale
The disproof is mathematically correct (independently brute-force verified over the complete antichain space), the formalization faithfully encodes finite graded posets, direct products, and the exact rational LYM inequality, and the final theorem contradicts the conjecture's first clause on its own objects. Fresh build exits 0 with only standard axioms and no forbidden constructs.

## Disposition
APPROVED — merged into main (PR 348). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
