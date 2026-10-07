# Solution Review — Conjecture 00000008482 (PR 626)

**Submission:** AlyciaBHZ — `solutions/00000008482/AlyciaBHZ_submission_20261005101836`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

| Check | Result |
|---|---|
| Official conjecture read (`conjectures/00000008482.md`, bilingual) | pass |
| LaTeX report read in full; rebuilt with `latexmk -pdf` | pass |
| Shipped vs rebuilt PDF text (pypdf, glyph-normalized) | pass |
| `lake build` (Lean v4.33.0, Mathlib db584cd6d4, prebuilt pool) | pass |
| Axiom audit (`#print axioms`, scratch checks; allowed set only) | pass |
| `verify.py` executed; output matches shipped `verification.txt` | pass |
| No `sorry`/`native_decide`/`admit`/`extern`/`unsafe`/`axiom` | pass |
| Faithfulness gate (conjecture's own objects, no surrogate) | pass |
| Semantic audit (exact quantifiers/objects) | pass |

Build facts: `lake build` exits 0 with no errors; the only reported axioms are
`propext`, `Classical.choice`, `Quot.sound` for this PR every audited theorem depends only on `propext`, `Classical.choice`, `Quot.sound`; the Lean source
SHA-256 in `verification.txt` matches the shipped source; the rebuilt PDF has the
same page count as the shipped one and identical extracted text modulo
ligature/smart-quote glyph-extraction artifacts introduced by font subsetting.

## Semantic audit

Decisive theorem is the negation of the formalized universal upper-bound clause with the witness family satisfying every hypothesis and the convergence premise; under the alternative reading the negation of the existence-of-extremal clause is proven for all families. Expectations are handled via deterministic families, which is exact, not a surrogate. verify.py numerically confirms subadditivity, stationarity, bounds, the exact error formula, and the diverging error/(log n/n) ratios.

## Issues found

None blocking. Minor: the universal clause formalized includes the Tendsto premise (needed because gamma is defined via limUnder); the witness satisfies it, so the refutation stands.

## Verdict

**APPROVED** — disproof.

The conjecture is a three-clause conjunction; the submission refutes it under every reasonable reading of the undefined word 'bounded'. Primary reading (bounded local costs / linear growth / bounded successive increments): the deterministic stationary family X_{m,n}=sqrt(n-m) is subadditive, has 0<=X<=n-m, unit one-step costs, increments bounded by 1, gamma=0, and convergence error exactly 1/sqrt(n), which is not O(log n/n) (sqrt n = O(log n) is impossible since log n = o(sqrt n)); this is fully formalized, including the big-O negation via Mathlib's isLittleO_log_rpow_atTop. Uniformly-bounded reading: the Lean proves every such family has error o(log n/n), so the claimed logarithmic sharpness (Sturmian extremal law) fails for every admissible family. Both results are combined in conjecture_00000008482_false_both_readings. The witness lives on a one-point probability space, hence is a legitimate (ergodic) subadditive process satisfying all stated restrictions simultaneously; the report is scrupulous about what is and is not refuted (e.g. does not claim the arbitrary-slowness clause is false).
