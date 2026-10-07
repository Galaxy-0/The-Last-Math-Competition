# Solution Review — Conjecture 00000000399 (PR 623)

**Submission:** AlyciaBHZ — `solutions/00000000399/AlyciaBHZ_submission_20261005101836`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

| Check | Result |
|---|---|
| Official conjecture read (`conjectures/00000000399.md`, bilingual) | pass |
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

The decisive theorem calkin_wilf_digit_golden_law contains the literal O(log n) statement (maxDigits n - n*log2 phi =O[atTop] log n) as a conjunct, plus strictly stronger exact statements (safe). Level-index convention (root at level 0 vs 1) only shifts the O(1) error, discussed in the report. verify.py regenerates the tree through level 17, cross-checks against an independently computed Stern sequence, and verifies the base-b bounds exactly through level 10000.

## Issues found

None blocking. Minor: 'digits' base was unspecified in the conjecture; the submission proves the law for every base and shows only base 2 matches the printed coefficient - strictly more information than required.

## Verdict

**APPROVED** — proof.

The submission proves the conjecture (binary-digit reading) with a stronger O(1) error: for the standard Calkin-Wilf tree (root (1,1) at level 0, children (a,a+b) and (a+b,b)), it proves in Lean the exact level maximum maxDen n = fib(n+2) (sharp invariant on coordinates and sums, attained by mirror-zigzag Fibonacci witnesses - this also realizes the 'branching geometry' clause), the exact digit maximum maxDigits n = floor(log2 fib(n+2))+1, the uniform bound |maxDigits n - n*log2(phi)| <= log2(phi)+1 for every n (hence the literal O(log n) assertion, formalized as the Mathlib IsBigO statement), plus an all-base generalization (slope log_b phi, O(1) error for every base b>=2) and the iff showing the printed log2 phi coefficient is valid only for base 2, with unbounded non-O(log n) error in every base b>=3. Faithful: the tree, levels, denominators (proved coprime, hence reduced), and digit counts are the conjecture's own objects; the base-2 reading is forced by the conjecture's own log2 phi coefficient. Math is independently sanity-checked (maxDen sequence 1,2,3,5,8,13,... matches Stern-sequence row maxima).
