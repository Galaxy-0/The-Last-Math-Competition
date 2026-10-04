# Solution Review — Conjecture 00000000141 (PR 429)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004083001`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff adds only the correctly named personal submission folder. Base metadata marks conjecture 00000000141 unsolved, and no prior/removed submission exists. The submitted bilingual `conjecture.md` is byte-identical to the official file.
- **LaTeX and PDF.** I read the complete three-page report and all submitted source/config files. Fresh `latexmk -pdf` compilation succeeded (exit 0; 3 pages). Text extraction, normalized comparison, and Ghostscript rendering confirmed that the shipped PDF matches the source/report content. No auxiliary numerical program is needed.
- **Lean.** Using the shared official pinned Mathlib tree, `lake build` succeeded. Direct strict replay of `Counting.lean`, `Growth.lean`, `Conjecture141.lean`, and `Check.lean` all exited 0. The audit prints the actual count, injection, asymptotic expression, exact source constant, and final negation. Nineteen central axiom audits use only standard foundational axioms; some use only a subset.
- **Forbidden-content scan.** No proof escape, custom axiom, unsafe declaration, implementation override, native decision shortcut, or kernel-trust override occurs. Only legitimate `#print axioms` commands contain “axioms”.
- **Independent mathematics.** I independently checked the factorial lower bound and the logarithmic growth gap on large even indices.

## Semantic audit

The conjecture concerns labelled permutations of `n` elements for which every cycle length is prime. Lean's `PrimeCycles` checks every part of the actual cycle partition, including length-one fixed-point parts; thus fixed points are correctly forbidden. `N(n)` is the cardinality of the finite subtype of actual permutations of `Fin n` satisfying that predicate, not a conjugacy-class or partition count.

For each permutation `σ` of `n` labels, take disjoint left/right copies of the label set and define

`τ(L_i)=R_{σ(i)}, τ(R_j)=L_{σ^{-1}(j)}`.

This map always switches copies, so it has no fixed point, and applying it twice gives the identity. Hence every cycle has length exactly two, which is prime. The construction determines `σ` from its values on the left copy, so it is injective. After an explicit relabelling to `Fin(2n)`, Lean obtains an injection from all `n!` permutations into the admissible subtype counted by `N(2n)`. Therefore `N(2n)≥n!` for every `n`.

Let

`g_c(k)=c k^{-1/2} exp(2√(k/log k))`.

For large `k`, `log k≥1`, so `2√(k/log k)≤2√k≤k` and `k^{-1/2}≤1`; hence `g_c(k)≤c e^k`. On even `k=2n`, this is at most `c(e^2)^n`. Factorials eventually dominate every fixed multiple of a geometric sequence. Consequently, along sufficiently large even indices,

`n!≤N(2n)<2g_c(2n)≤2c(e^2)^n<n!`,

a contradiction. This refutes the ratio limit and asymptotic equivalence for every positive `c`, including the exact printed constant `(4π)^{-1/2}e^{-1/2}`. Lean uses Mathlib's actual `Asymptotics.IsEquivalent`, proves eventual positivity needed to pass to the quotient, restricts along the cofinal even subsequence, and negates the exact conjecture predicate.

The lower bound is non-vacuous and constructive; it does not rely on a guessed total enumeration formula. Refuting the displayed asymptotic suffices, regardless of the later capacity-integral phrase.

## Verdict rationale

The formal count and asymptotic predicate match the official statement. The even-index factorial family gives a decisive infinite-family obstruction to the proposed subexponential asymptotic, and every build, replay, axiom audit, scan, and hash check passes.

## Disposition

APPROVED — ready for merge (PR 429). No merge action was taken by this reviewer.
