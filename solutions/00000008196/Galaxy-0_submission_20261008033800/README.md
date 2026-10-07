# Dependent Staudt hits at 5 and 17

Conjecture 00000008196 explicitly calls the events p−1 dividing k independent. For k=2n, the hits at the distinct primes 5 and 17 are respectively 2 dividing n and 8 dividing n. They are nested. On every uniform cutoff n=1,…,8m with m≥1, their counts are 4m and m, and the joint count is m. Thus the joint probability is 1/8, whereas the product of marginals is 1/16.

## Interpretation and scope

The source does not specify a probability space. This submission refutes its independence clause under the standard uniform-positive-even-cutoff and natural-density interpretation. It does not assert that every conceivable probability law fails: a degenerate law can make one event certain or the other impossible. The same dependence also occurs for natural-density sampling of all positive indices.

No Bernoulli-number implementation or von Staudt–Clausen theorem is required, because the source itself supplies the hit predicate p−1 dividing k. No claim is made about the other expectation or numerator-distribution clauses.

The formal result is exact arithmetic at finite cutoffs and an unbounded family of sample sizes. Real-limit and measure-theoretic interpretations are explained in the written report, not claimed as a separate Lean probability development.

## Reproduce

With the official pinned Lean toolchain installed:

    lake build
    lake env lean -DwarningAsError=true Main.lean
    python3 check_counts.py
    bash build-pdf.sh

The Lean project imports only the bundled standard library and has no external package dependencies. A normal LaTeX installation with AMS fonts and hyperref builds the report.

## Contents

- `Main.lean`: real divisibility predicates, periodic counting and formal counterexample
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`: reproducible project
- `proof.tex`, `proof.pdf`: mathematical proof and formalization boundary
- `check_counts.py`: independent finite-count regression checks
- `source.md`: original bilingual statement
- `verification/`: actual build and axiom logs, independent review and eligibility checks

All changes are confined to this personal submission directory. AI-assisted submission by Galaxy-0, for independent competition review.
