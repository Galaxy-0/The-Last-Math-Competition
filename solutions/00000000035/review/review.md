# Solution Review — Conjecture 00000000035 (PR 468)

**Submission:** jilint777 — `jilint777_submission_20261004055354`
**Reviewer:** independent competition review (finite combinatorics, build, exhaustive computation)
**Date:** 2026-10-04

## Checklist
- [x] Official bilingual conjecture read; literal two-color reading matched
- [x] Full LaTeX source and three-page PDF read; independent PDF build passed
- [x] Full self-contained Lean project independently rebuilt
- [x] Direct warnings-as-errors Lean check passed
- [x] Only standard foundational axioms reported
- [x] Auxiliary exhaustive program rerun and independently reimplemented
- [x] No incomplete-proof marker, native decision tactic, custom axiom, unsafe construct, external hook, or kernel bypass
- [x] Submission adds only its own correctly named folder
- [x] Conjecture unsolved in base metadata

## Result
The conjecture is true with \(N=17\). In fact, every 2-coloring of \([17]\) contains a monochromatic triple \((x,y,x+y)\) with the stronger restriction \(1\le x<y\), \(x+y\le17\), and \(xy+1\) prime.

There are exactly 31 such triples. The report gives a complete twelve-branch case analysis: under the assumption that all are non-monochromatic, two equal colors in any listed triple force the opposite color on the third entry. Both choices at every branch split are pursued, and every branch ends at a listed triple forced to be monochromatic.

## Formal audit
Lean uses the standard divisor definition of primality and proves its trial-division checker correct in both directions. `SchurPrimeTriple` contains every required inequality, equation, interval bound, and primality condition. `schur_17` formalizes the entire DPLL case analysis using proved Boolean propagation lemmas. The final theorem supplies \(N=17\) uniformly for every otherwise-unused parameter \(k\); a separate interval-subtype theorem matches colorings literally defined only on \([N]\).

A fresh `lake build` and direct warnings-as-errors elaboration both passed. The final theorems use only `propext`, `Classical.choice`, and `Quot.sound`; the sharpness theorem uses only `propext` and `Quot.sound`.

## Independent computation
The supplied Python script exhaustively checked all \(2^{17}\) colorings and passed. It found 31 strict triples at \(N=17\), no avoiding coloring at 17, 23 strict triples and an avoiding coloring at 16, and threshold 7 when \(x=y\) is allowed.

I separately reimplemented the brute-force search. It independently found zero avoiding colorings at 17, 28 at 16, strict threshold 17, nonstrict threshold 7, and confirmed the submitted sixteen-point coloring avoids every strict triple.

## Sharpness
The explicit coloring `0010101110110101` of \([16]\) avoids all 23 strict triples, so 17 is optimal for the stronger \(x<y\) reading. This sharpness is additional; the conjecture only requires some finite \(N\).

## Verdict
APPROVED — ready for integration as the first valid solution.
