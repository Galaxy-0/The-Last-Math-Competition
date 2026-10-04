# Local verification record

This records author-side execution and independent internal scrutiny, not official maintainer acceptance.

## Mathematical coverage

Both contribution guides and the exact bilingual conjecture were checked at upstream `4cc82278ba1e5becc4d20b1e2a68dede094e2b8d`. The source leaves the coefficient field and nondegeneracy definition unstated; the report explicitly uses the standard linear-recurrence convention and cites a primary reference. Neither source language excludes integral terms.

- The sequence is the actual function `2^n + r^n`. Its actual Mathlib `LinearRecurrence` has order two and coefficient vector `(-2*r, 2+r)`. The satisfaction equation is proved for every index.
- The actual characteristic polynomial is `(X-2)*(X-r)`, and its complete complex root set is proved after mapping the polynomial into the complex numbers. All roots are nonzero and every distinct-root quotient has infinite multiplicative order for the positive parameters used here.
- Minimality is proved against every competing real recurrence. An order-zero recurrence contradicts the initial value; an order-one recurrence forces `(r-2)^2=0`, contradicting both chosen parameters.
- Distance is `Metric.infDist` to the actual range of the integer embedding into the reals. Its equality to distance from the rounded nearest integer is proved using both inequalities and nonemptiness of that set.
- For `r=1/3`, every positive-index distance equals `(1/3)^n` and is strictly positive. All terms are rational; the sequence tends to infinity. For every real C the product `n^C*(1/3)^n` tends to zero, giving the strict reverse inequality on a full tail. This contradicts every proposed exponent C and starting index N.
- For `r=3`, all terms are integers and the distance is zero. This refutes the asserted strict lower bound even under a monic integer-coefficient, integer-initial-data convention. It is a separate supplemental disproof; the main example has nonintegral positive-index terms.
- The final theorems negate the universal existence assertion over actual minimal nondegenerate recurrences. All witness hypotheses are discharged. Refuting existence also refutes the stronger request for an explicit root-gap rule; no unspecified rule is invented.

## Fresh independent execution

A separate verification agent copied only the six final Lean files and three configuration files to `/private/tmp/tlmc367-independent`. No compiled submission outputs were copied. The existing cache of pinned dependencies was reused; this is not a rebuild of all Mathlib dependencies from source.

| Check | Result |
|---|---|
| Lean compiler | 4.19.0, exact commit `6caaee842e9495688c1567e78c0e68dbb96942aa` |
| Mathlib | v4.19.0, exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| All nine dependency revisions | Exact manifest matches; tracked sources clean before and after |
| Fresh complete `lake build` | Exit 0 |
| Direct strict replay of all six Lean files | All exit 0, warnings treated as errors |
| Actual definition printouts | All seven present |
| Actual type and transitive-axiom audits | All 35 named theorems present |
| Allowed axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound` |
| Proof-bypass scan | No code matches |
| Source/config identity | All nine files identical and unchanged across both directories |

`verification/strict-replay.json` records exact commands, outputs, compiler identity, source hashes, dependency revisions and parsed audit results. `verification/build.txt` and `verification/axioms.txt` preserve the actual outputs. Every strict replay used `lake env lean -DwarningAsError=true`. All expected names are matched against actual declaration types, definitions and axiom output. No numerical auxiliary computation is needed: recurrence identities, nearest-integer distance and the asymptotic argument are proved in Lean.

## Report and independent review

The exact final `main.tex` compiles successfully with the desktop editor compiler and Tectonic 0.17.0. Both pages of the exported PDF were rendered with Poppler and visually inspected in full. Text, formulas and references are legible, with no clipping, overlap, missing glyphs, blank page or orphan reference page. The TeX log contains no warnings or overfull/underfull boxes. Text extraction provides a secondary content check; visual inspection is the layout check.

`verification/pdf.json` records the exact source/PDF hashes and the visual inspection scope; `verification/report.txt` preserves the TeX log with trailing whitespace removed. `SEMANTIC_REVIEW.md` records a separate agent's full mathematical/source/report scrutiny and exact reviewed identities. That internal semantic review is distinct from the fresh compilation performed by the verification agent and the coordinating agent's PDF visual inspection.

## Eligibility and submission identity

`verification/eligibility.json` preserves the initial upstream source/rule identity, unsolved metadata, all-state PR and comment searches, topic-match classification, and current/historical solution-path checks. The initial scan covered 541 PRs through #545 and found no prior or competing submission for 00000000367. Bare PR #367 concerns another conjecture. No prior-error account is applicable to the checked records. The final live refresh is preserved separately in `verification/prepublication.json`.

Only the personal submission directory is changed. The package contains no dependency folders, compiled Lean artifacts, or scratch probes. `verification/SHA256SUMS.json` covers every other submitted file; its hashes are checked against the exact staged Git bytes before commit. Timestamps are evidence of checks performed, not guarantees against subsequent repository changes.
