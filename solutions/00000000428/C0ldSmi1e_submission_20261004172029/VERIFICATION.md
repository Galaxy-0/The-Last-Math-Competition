# Local verification record

These are author-side execution records and an independent internal semantic review. They are distinct from official competition review and maintainer acceptance.

## Mathematical coverage

The exact English and Chinese statement and both contribution guides were checked at upstream `4cc82278ba1e5becc4d20b1e2a68dede094e2b8d`.

- The sample space is the actual Mathlib type `Nat.Partition n`, whose positive parts retain multiplicities and sum to `n`. Its standard finite-type and inhabited instances are used.
- `rowsAtLeast` counts actual parts at least a proposed square side. The finite set of possible sides contains zero; its finite cutoff is proved redundant. `durfee` is its attained maximum, with a global maximal-square characterization.
- `ferrers` is an actual Mathlib `YoungDiagram`. The proof establishes its exact untruncated membership condition, downward closure, square containment if and only if the side is at most `durfee`, and actual diagram cardinality `n`.
- The filtered multiset sum proves `durfee p ^ 2 ≤ n`, hence the real square-root bound for every actual partition.
- `partitionPMF` is `PMF.uniformOfFintype`. `partitionMeasure` is its actual probability measure, with equal singleton masses. The Durfee statistic is measurable and integrable; `meanDurfee` is its integral. The arithmetic-mean formula is proved from that probability law, and integral monotonicity gives `meanDurfee n ≤ √n`.
- The displayed leading term is retained exactly, with coefficient `√(6n)/π` and the natural logarithm. The proof establishes divergence of its excess over the actual mean, excluding every finite constant correction.
- `ClaimedExpansion` is the existential assertion that the exact remainder after subtracting the proposed leading term and some real constant tends to zero. `conjecture_false` negates it with no extra assumptions. This is a full infinite-limit disproof, not extrapolation from finitely many computed partitions.

## Fresh build in an independent directory

Only the five final Lean files and three configuration files were copied to `/private/tmp/tlmc428-independent`. No compiled submission outputs were copied. The existing cache of pinned dependencies was reused; this is not a claim to rebuild all Mathlib dependencies from source.

| Check | Result |
|---|---|
| Lean compiler | 4.19.0, exact commit `6caaee842e9495688c1567e78c0e68dbb96942aa` |
| Mathlib | v4.19.0, exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| All nine manifest dependencies | Exact revisions match; tracked trees clean before and after |
| Fresh complete `lake build` | Exit 0 |
| Strict replay of Partitions, Expectation, Asymptotics, root and Check | All five exit 0 |
| Definition and instance printouts | All 13 present |
| Type and transitive-axiom audits | All 38 present: 35 theorems/lemmas and three named instances |
| Axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound` |
| Proof-bypass source scan | No code hits; a raw keyword in a Check comment is recorded as an ignored comment |
| Original and independent-copy hashes | All eight identical and unchanged |

Every strict replay used `lake env lean -DwarningAsError=true`. `verification/strict-replay.json` records exact commands, outputs, exit codes, source hashes, compiler identity, dependency revisions, and parsed audit results. The actual build and definition/type/axiom outputs are preserved separately in `verification/build.txt` and `verification/axioms.txt`. The audit parser supports declarations with no axiom dependencies as well as explicit axiom lists; all 38 actual outputs in this run list only standard foundational axioms.

No numerical auxiliary program is needed: all mathematical computations and the limiting contradiction are proved in Lean. The internal semantic reviewer separately inspects the exact source, report, definitions, quantifiers and completed execution evidence; its scope and exact reviewed hashes appear in `SEMANTIC_REVIEW.md`.

## Report and file identity

The exact final LaTeX source compiles with both the desktop editor compiler and Tectonic 0.17.0. The exported PDF has two substantive pages. Both pages were rendered with Poppler and visually inspected in full, including the claim, definitions, uniform mean formula, square-area argument, limit proof, formal correspondence and reference. No TeX warnings, clipping, overlap, missing glyphs, blank pages or orphan references were found. Text extraction additionally checked key content.

`verification/pdf.json` records the source/PDF hashes and visual checks. `verification/report.txt` preserves the successful TeX log with trailing whitespace removed. The submitted source and PDF are byte-identical to the exported and inspected pair.

Only the personal submission directory is changed. `verification/SHA256SUMS.json` covers every other submitted file, and its hashes are checked against the exact staged Git bytes. Scratch probes, dependency directories, and compiled Lean artifacts are excluded.

## Eligibility

`verification/eligibility.json` preserves the initial check of unsolved metadata, exact source/rule identities, all-state PR title/body/head searches, padded and short ID/comment searches, topic searches, and current/historical solution paths. False matches are classified explicitly: PR number 428 concerns conjecture 973; a decimal `0.428` appears in an unrelated semigroup submission; the Gumbel keyword appears in a random-matrix gap submission.

No prior, removed, successful or competing submission for conjecture 00000000428 was identified, so no prior-error account applies. A final live refresh is preserved separately in `verification/prepublication.json`.
