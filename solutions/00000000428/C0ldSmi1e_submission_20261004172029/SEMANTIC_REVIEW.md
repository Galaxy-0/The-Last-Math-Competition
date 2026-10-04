# Internal semantic review: conjecture 00000000428

**Verdict: PASS for the frozen proof and report identified below.** No mathematical or semantic correction is required. The final theorem proves the negation of the displayed additive asymptotic for the actual uniform-partition Durfee expectation.

This is an independent internal source review by a separate reviewing agent, not official maintainer acceptance or a competition `review/` decision. I read the complete five-file Lean source, three project configuration files, complete LaTeX report, exact bilingual conjecture, both upstream contribution guides, relevant Mathlib definitions, and completed verification records. The fresh compilation was executed by a separate verification agent; I inspected its actual output and independently checked its source identities and audit counts. PDF compilation and visual inspection were performed separately by the coordinating agent, as distinguished below. I did not modify the mathematical sources or report.

## Statement and standard interpretation

The English and Chinese versions both assert

\[
\mathbb E[d(\text{uniform partition of }n)]
=\frac{\sqrt{6n}}{\pi}\log\!\left(\frac{\sqrt{6n}}{\pi}\right)+c+o(1).
\]

Here the Durfee size is the **side length** of the largest square in a partition's Ferrers diagram, and the constant is independent of n. This is the standard convention: [Pak–Panova, §2.1](https://www.math.ucla.edu/~pak/papers/Fixed12.pdf) defines it by the largest k with the kth part at least k. The uniform interpretation gives equal weight to every integer partition of the fixed integer n; [§4 of the research article on Plancherel averages](https://link.springer.com/article/10.1007/s44007-023-00061-2) explicitly distinguishes that uniform measure from Plancherel measure. These references support definitions only; no external asymptotic theorem is needed by this submission.

There is no source hypothesis restricting the partitions, changing the statistic to square area, or making c depend on n. The phrase about a Gumbel-type correction does not change the displayed necessary assertion. The proof addresses that assertion exactly and does not claim a replacement asymptotic or a distributional limit.

## Actual partitions and Ferrers squares

`Nat.Partition n` is Mathlib's multiset of positive natural parts with sum n. Its finite-type and inhabited instances are supplied by Mathlib, including the unique empty partition at n=0. `rowsAtLeast` filters that multiset, so repeated parts remain counted with their multiplicities. No restriction to distinct parts, ordered compositions, or tableaux is introduced.

`squareSides` initially searches 0 through n. Zero belongs, and `mem_squareSides_iff` proves the cutoff redundant for every natural k. `durfee_attained`, `le_durfee_of_square`, and `square_iff_le_durfee` establish attainment and global maximality. Thus the definition is the full Durfee side length, not a truncated statistic or a convenient bound assigned that name.

`ferrers` is an actual Mathlib `YoungDiagram`, a finite lower set in the product order on natural-coordinate cells. Its unrestricted membership theorem says column j has exactly as many cells as there are parts at least j+1. This is the canonical Ferrers construction from the partition's column heights. The finite n-by-n representation is proved not to omit cells. `sum_column_counts` counts every occurrence of every part, and `ferrers_card` proves the resulting diagram has exactly n cells. Finally,

\[
\{0,\ldots,k-1\}^2\subseteq F(p)\quad\Longleftrightarrow\quad k\le d(p)
\]

holds for every natural k. This is an actual square-containment equivalence, including k=0. The area inequality is independently derived by bounding the sum of the filtered original parts below by k times its cardinality and above by n. In particular, `durfee_sq_le` and `durfee_le_sqrt` prove the correct deterministic bounds without an assumed area hypothesis.

## Uniform probability and expectation

The measurable space on `Nat.Partition n` is the full power-set sigma algebra. `partitionPMF` is Mathlib's `PMF.uniformOfFintype`; nonemptiness prevents a vacuous or zero-mass model. `partitionMeasure` is its actual associated measure, with a proved probability-measure instance. Both the PMF and singleton-measure theorems assign each partition the reciprocal of the number of partitions.

The statistic is explicitly proved measurable and integrable. `meanDurfee` is its real Bochner integral against this measure. `meanDurfee_eq_average` derives, from the PMF integral theorem, the arithmetic mean over all partitions. The proof therefore does not substitute an unrelated sequence for an expectation. `meanDurfee_nonneg` and `meanDurfee_le_sqrt` prove the interval bound on this actual integral. In particular the integral's totalized value outside integrability is never used.

## Exact limiting contradiction and quantifiers

`scale` is exactly sqrt(6*n)/pi over the reals and `mainTerm` multiplies it by its natural logarithm. `scale_eq` relates it to a*sqrt(n), where a=sqrt(6)/pi is proved strictly positive. Real square roots along the natural numbers, this scale, and then its logarithm tend to positive infinity.

The proof eventually has log(scale n) at least 2/a, so the exact main term is at least 2*sqrt(n). Every sequence f bounded above by sqrt(n) therefore satisfies mainTerm(n)-f(n) tending to positive infinity. Specialization uses the already proved bound on `meanDurfee`. The auxiliary theorem's only bound hypothesis is discharged; the final result has no extra hypotheses.

`no_finite_additive_correction` excludes convergence of meanDurfee-mainTerm to every real c. `ClaimedExpansion` quantifies existentially over an arbitrary real c and asserts that meanDurfee-(mainTerm+c) tends to zero. This is exactly the additive o(1) assertion. `conjecture_false` negates it by adding c to the putative vanishing remainder. This is a genuine infinite-limit contradiction, not a finite numerical counterexample, a special choice of c, or merely a failure of a weaker asymptotic relation. Totalized real logarithms at small n do not affect the atTop argument.

## Report, execution evidence, and rule scope

The complete report matches these definitions, proofs, and quantifiers. Its added statement that the Ferrers diagram has n cells is proved by `ferrers_card`. The report's elementary proof uses the same eventual factor-two bound as Lean. Its empty-partition convention, uniform mean, coefficient, and logarithm all agree with the code.

The completed `strict-replay.json`, `build.txt`, and `axioms.txt` record a fresh independent project build and strict replays of all five Lean files with warnings treated as errors; all six invocations exit successfully. The exact Lean 4.19.0 commit is `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine dependency revisions match the manifest and their tracked trees are clean before and after execution. The copied project initially had no local build products.

I checked the actual Check output against the Check source: all 13 definition/instance printouts and all 38 type/axiom audits are present (35 theorems/lemmas and three named instances). Every listed axiom belongs to `propext`, `Classical.choice`, and `Quot.sound`. The proof-bypass scan has no code hits; its sole raw match is the word “axiom” in a Check comment. All eight original, independent-copy, and managed-package source/config hashes agree and are unchanged. No auxiliary numerical program supplies a mathematical claim.

The separately produced `pdf.json` records successful native and Tectonic compilation of the exact final TeX, two rendered pages, and the coordinating agent's inspection of both pages without visual defects. I read that record and the compilation log and independently verified the managed TeX and PDF hashes. I did not personally perform a second visual inspection, so the layout finding is attributed to that recorded inspection.

Both contribution guides at upstream `4cc82278ba1e5becc4d20b1e2a68dede094e2b8d` were read. The reviewed eligibility evidence records unsolved metadata, no matching earlier submission, no solution-path history, and searches of 519 all-state PR records through #523. Incidental short-ID/Gumbel search matches were classified as different conjectures. These are timestamped eligibility findings, not a guarantee against later submissions; final prepublication refresh and PR path-only checks belong to the coordinating task. The intended submission is the personal folder `solutions/00000000428/C0ldSmi1e_submission_20261004172029`. This internal review does not authorize or claim a merge, metadata change, or official acceptance.

## Exact reviewed identities

Hashes are SHA-256 of the actual bytes inspected. Paths beginning `lean/` are relative to the personal submission and match the scratch and independent-build copies.

| File | SHA-256 |
|---|---|
| `lean/Conjecture428/Partitions.lean` | `18bdcc0f4b89d8d27027e5bb33c15caa7c0665cbc2da25028038954a9cf67c72` |
| `lean/Conjecture428/Expectation.lean` | `68d6ce72720480f171d5f3c7fa1ff50d2414dbdd1017752e88cbabcfc7ee8ee1` |
| `lean/Conjecture428/Asymptotics.lean` | `9fb744f80cafdd9440d3a04d04dadad16ad3ea448db3fb97f97fe2717711a1cb` |
| `lean/Conjecture428.lean` | `0ffa441591d6e3ab582aafa1c8e9c125afaf5dbadb6251518ff7d0e0679570f2` |
| `lean/Check.lean` | `ad58da0a4f93beac8f721638e28f8cedbd8d61c2a24a4d8ae5ee38042203e30e` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `lean/lakefile.toml` | `5f3cb9630696f93e8b90900c446dec6e50d1aaa57e475818b3267a3cbe1cc911` |
| `lean/lake-manifest.json` | `9c000ecf0c0506db02d5bf000820610b52255d2e2f3a5bf33b64e9123dd1f7b9` |
| `main.tex` | `bad0c2a6f088169e62d91d3acfdcf1abedd38ec8faba51c7f1c016bc663de038` |
| `main.pdf` | `5fe97de2830e7081a4ffd48377147e0b270e17ec298658465f461427d5348ebe` |
| `conjecture.md` | `22b6038304b6987c15b6c601d3c4b6392401a50be3b88e6226ecb20816cd2dd3` |
| `upstream README.md` | `f7df38cc270f58a323726aaa98535a26a447a59b801a89dca371460e2f852186` |
| `upstream README.zh-CN.md` | `2b044eeb742eb45a4607e55edd82471e975f8c01e376ba5313c128fcf0d301ae` |
| `strict-replay.json` | `7baecb10f37ef7893e8be552ace2c975274611ab1c39ff931b217ece224338e5` |
| `build.txt` | `026a4b95b535a09604acd2743b46c30d13ac2fae25689488b20045cd8896b726` |
| `axioms.txt` | `bd47def859a35878641e5622f8a1ed429d1831d1d397895a7bfc3e5135e054d0` |
| `pdf.json` | `d663157b17f173158b4db5eb901eb1ebea294b3a7fbd0aa042e06d3bdcd9d75c` |
| `eligibility.json` | `89d0c7f6c067d80f2dcb5c67823550d6ffe9bf801969c4e09b8a47af9463a7fd` |

Review completed: 2026-10-04T17:23:41.679065+00:00.
