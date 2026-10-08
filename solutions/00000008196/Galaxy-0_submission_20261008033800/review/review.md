# Solution Review — Conjecture 00000008196 (PR 844)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261008033800`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-08

## Checklist results
- Conjecture read: yes — the source asserts (among other clauses) that the Staudt hits of primes `p` (defined by `p − 1 ∣ k`) are **independent** ("an independent hit law").
- Change scope: only `solutions/00000008196/Galaxy-0_submission_20261008033800/` was added; the conjecture is unsolved in the base metadata.
- LaTeX: `proof.tex` read in full. The argument is elementary and complete.
- Lean build: Lean 4.31.0, standard-library-only project (no external dependencies). `lake build` exit 0; the project sets `warningAsError` and builds cleanly.
- Forbidden content: none.
- Auxiliary code: `check_counts.py` re-run independently — "PASS: primality, nested events, exact counts for N=1..1000; all 125 multiples of 8 have discrepancy 1/16."

## Semantic audit
Using only the divisibility predicate supplied by the conjecture itself, the submission considers the distinct primes `5` and `17` and the positive even indices `k = 2n`. Then the hit at `5` is `4 ∣ k ⟺ 2 ∣ n` and the hit at `17` is `16 ∣ k ⟺ 8 ∣ n`, so the second event is contained in the first. On the initial segment `{2,4,…,16m}` the counts are `4m`, `m`, and `m`, giving `P(hit5) = 1/2`, `P(hit17) = 1/8`, `P(both) = 1/8 ≠ 1/16 = (1/2)(1/8)`. Independence fails at every sample size, so it also fails in the natural-density limit. The report further proves the distribution-free obstruction: for nested events `B ⊆ A`, independence forces `P(B) = 0` or `P(A) = 1`.

The Lean project (`Main.lean`, standard library only) formalizes the literal predicate `hit p k = (k % (p-1) == 0)`, proves `hit 17 k → hit 5 k`, proves exact periodic counts per block and the exact counts `exact_counts` for the first `8m` even indices, defines `IndependentOn` as the cross-multiplied independence identity, and proves `not_independent`, `arbitrarily_large_counterexamples`, and `conjecture8196_false : ¬ IndependentHitLaw`. All are kernel-checked with only `propext` and `Quot.sound`.

## Issues found
- The conjecture does not specify a probability space; the submission is explicit that it refutes the independence clause under the standard uniform-positive-even-cutoff / natural-density interpretation, and that a degenerate law could make the events trivially independent. This is stated honestly and the accompanying general nested-events argument makes the obstruction robust.

## Verdict rationale
Under the natural (and only reasonable) interpretation of the underspecified independence clause, the two hit events are nested and hence dependent; the Lean formalization rigorously establishes the exact finite counts and the failure of independence for an unbounded family of sample sizes, with no forbidden content and only the two standard axioms.

## Disposition
APPROVED — ready to merge (PR 844).
